-- Prove2me | Definitions.Def_ActiveSaddleSGD_ProjectedIterates
-- name    : ActiveSaddleSGD_ProjectedIterates
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:09:25.882721+00:00
-- url     : https://prove2.me/theorems/a4da8442-1f94-472f-8860-2ea1a30ef569
-- title:
--   The projected iterates $y_n^N$, the residuals $z_n^N$, the noise $\tilde\eta_n^N$ and $\chi_n$
-- statement:
--   Let $r>0$ be small, $P_M$ the projection on $M$, single-valued and $C^4$ near $x^*$, and $D$ a bounded continuous extension of $\nabla(F\circ P_M)$. For $N\ge1$ let $\tau_N=\inf\{n\ge N:\|x_n-x^*\|>r\}$, with $\inf\emptyset=\infty$. The process $(y_n^N)_{n\ge N-1}$ is given by $y_{N-1}^N=x^*$ and
--   $$
--   y_n^N=\begin{cases}P_M(x_n)&N\le n<\tau_N,\\ y_{n-1}^N-\gamma_{n-1}D(y_{n-1}^N)+\gamma_{n-1}J_{P_M}(y_{n-1}^N)\eta_n&n=\tau_N,\\ y_{n-1}^N-\gamma_{n-1}D(y_{n-1}^N)+\gamma_{n-1}\eta_n&\text{otherwise.}\end{cases}
--   $$
--   The residual is $z_n^N=(x_n-y_n^N)\mathbb 1_{n<\tau_N}$ for $n\ge N$, the noise is
--   $$
--   \tilde\eta_{n+1}^N=(\mathbb 1_{\tau_N>n}J_{P_M}(y_n^N)+\mathbb 1_{\tau_N\le n})\eta_{n+1},
--   $$
--   and $\chi_n=\sum_{i\ge n}\gamma_i^2$.
--
--   These objects turn the nonsmooth iteration into a smooth stochastic approximation on $M$ with small perturbations.
--
--   **Formalization Note** `IsProjectionOn` packages "$P_M$ is single-valued and $C^4$ on the ball" for a total map $P$. `StayedIn` is the event $[n<\tau_N]$. `projResidual` is written $(x_n-P(x_n))\mathbb 1_{n<\tau_N}$, which is the same process and does not depend on $D$. `IsProjectedField` requires $D$ to agree with $\nabla(F\circ P)$ on the closed ball of radius $2r$, not $r$: the points $P(x)$, $\|x-x^*\|\le r$, lie there, and the proof of Proposition 4 evaluates $D$ at them. `tailChi` is a real series, meaningful when $\sum\gamma_i^2<\infty$.
-- source:
--   Bianchi, Hachem & Schechtman, Stochastic Subgradient Descent Escapes Active Strict Saddles on Weakly Convex Functions, arXiv:2108.02072v4, p.16, p.18, and (16), p.20

import Mathlib
import Definitions.Def_RandomGradFree_Nonsmooth_IsMetricProjection

open RandomGradFree.Nonsmooth MeasureTheory

namespace ActiveSaddleSGD

variable {d : ℕ} {Ω : Type*}

/-- Bianchi, Hachem & Schechtman, arXiv:2108.02072v4, Lemma 2, p.17 and p.18: on `B(x*, r)` the
projection `P_M` is single-valued, given by the map `P`, and `C⁴`.

**Formalization Note** `P` is a total function; only its values on the ball are constrained. The
paper's `x* = 0` is kept general throughout. -/
def IsProjectionOn (M : Set (EuclideanSpace ℝ (Fin d)))
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (xs : EuclideanSpace ℝ (Fin d)) (r : ℝ) : Prop :=
  (∀ x ∈ Metric.ball xs r, {z | IsMetricProjection M x z} = {P x}) ∧
    ContDiffOn ℝ 4 P (Metric.ball xs r)

/-- Bianchi, Hachem & Schechtman, arXiv:2108.02072v4, p.18: `D` is a bounded continuous extension of
`∇(F ∘ P_M)`.

**Formalization Note** The page extends from `B(0, r)`. Since `x* ∈ M`, the points `y = P_M(x)`
with `x ∈ B(x*, r)` lie in `B(x*, 2r)` and may leave `B(x*, r)` if `M` is curved, while the
proof of Proposition 4 uses `D(y) = ∇_M f(y)` at these `y`; a merely continuous `D` gives no control
outside the ball where it agrees with the gradient. So agreement is required on the closed ball of
radius `2r`. -/
def IsProjectedField (F : EuclideanSpace ℝ (Fin d) → ℝ)
    (P D : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (xs : EuclideanSpace ℝ (Fin d)) (r : ℝ) : Prop :=
  Continuous D ∧ (∃ B, ∀ y, ‖D y‖ ≤ B) ∧
    Set.EqOn D (gradient (F ∘ P)) (Metric.closedBall xs (2 * r))

/-- Bianchi, Hachem & Schechtman, arXiv:2108.02072v4, p.18: the event `[n < τ_N]`, where
`τ_N = inf{n ≥ N, ‖x_n‖ > r}`, written "the iterates stayed in the ball from `N` to `n`".

**Formalization Note** `x* = 0` on the page, so `‖x_n‖` becomes `‖x_n − x*‖`. For `n < N` the
condition is empty, in agreement with `τ_N ≥ N`. -/
def StayedIn (x : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (xs : EuclideanSpace ℝ (Fin d)) (r : ℝ)
    (N n : ℕ) (ω : Ω) : Prop :=
  ∀ k, N ≤ k → k ≤ n → ‖x k ω - xs‖ ≤ r

open Classical in
/-- Bianchi, Hachem & Schechtman, arXiv:2108.02072v4, p.18: the process `(y_n^N)`, with
`y_{N-1}^N = x*` (the paper's `0`), `y_n^N = P_M(x_n)` if `N ≤ n < τ_N`,
`y_n^N = y_{n-1}^N − γ_{n-1} D(y_{n-1}^N) + γ_{n-1} J_{P_M}(y_{n-1}^N) η_n` if `n = τ_N`, and
`y_n^N = y_{n-1}^N − γ_{n-1} D(y_{n-1}^N) + γ_{n-1} η_n` otherwise.

**Formalization Note** The process is meant for `N ≥ 1`, since `γ_{N-1}` is undefined at `N = 0`;
the events `𝒜_N` increase, so nothing is lost. All values before `N - 1` are `x*` and are not used.
`J_{P_M}` is `fderiv ℝ P`. -/
noncomputable def projIter (x η : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (γ : ℕ → ℝ)
    (xs : EuclideanSpace ℝ (Fin d)) (P D : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (r : ℝ) (N : ℕ) : ℕ → Ω → EuclideanSpace ℝ (Fin d)
  | 0, _ => xs
  | n + 1, ω =>
    if n + 1 < N then xs
    else if StayedIn x xs r N (n + 1) ω then P (x (n + 1) ω)
    else if StayedIn x xs r N n ω then
      projIter x η γ xs P D r N n ω - γ n • D (projIter x η γ xs P D r N n ω)
        + γ n • (fderiv ℝ P (projIter x η γ xs P D r N n ω)) (η (n + 1) ω)
    else
      projIter x η γ xs P D r N n ω - γ n • D (projIter x η γ xs P D r N n ω) + γ n • η (n + 1) ω

open Classical in
/-- Bianchi, Hachem & Schechtman, arXiv:2108.02072v4, p.18: `z_n^N = (x_n − y_n^N) 𝟙_{n<τ_N}` for
`n ≥ N`.

**Formalization Note** On `[n < τ_N]`, `n ≥ N`, the page has `y_n^N = P_M(x_n)`, so
`z_n^N = (x_n − P(x_n)) 𝟙_{n<τ_N}`, which is what is written here; `z` does not depend on `D`. It is
set to `0` for `n < N`, where the page does not define it. -/
noncomputable def projResidual (x : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (xs : EuclideanSpace ℝ (Fin d)) (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (r : ℝ) (N n : ℕ) (ω : Ω) : EuclideanSpace ℝ (Fin d) :=
  if N ≤ n ∧ StayedIn x xs r N n ω then x n ω - P (x n ω) else 0

open Classical in
/-- Bianchi, Hachem & Schechtman, arXiv:2108.02072v4, equation (16), p.20: the noise
`η̃_{n+1}^N = (𝟙_{τ_N>n} J_{P_M}(y_n^N) + 𝟙_{τ_N≤n}) η_{n+1}`, where `y` stands for `(y_n^N)`.

**Formalization Note** The value at index `0` is `0` and is not used. -/
noncomputable def noiseTilde (x η : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (xs : EuclideanSpace ℝ (Fin d)) (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (y : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (r : ℝ) (N : ℕ) : ℕ → Ω → EuclideanSpace ℝ (Fin d)
  | 0, _ => 0
  | n + 1, ω =>
    if StayedIn x xs r N n ω then (fderiv ℝ P (y n ω)) (η (n + 1) ω) else η (n + 1) ω

/-- Bianchi, Hachem & Schechtman, arXiv:2108.02072v4, p.16 and Proposition 3, p.17:
`χ_n = Σ_{i=n}^∞ γ_i²`.

**Formalization Note** A real `tsum`: it is meaningful under `Σ γ_i² < ∞`, which holds under
Assumption 1 iv) and is assumed in Proposition 3. -/
noncomputable def tailChi (γ : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑' i, γ (n + i) ^ 2

end ActiveSaddleSGD


