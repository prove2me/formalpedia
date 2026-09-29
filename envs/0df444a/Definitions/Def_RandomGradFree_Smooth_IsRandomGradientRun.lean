-- Prove2me | Definitions.Def_RandomGradFree_Smooth_IsRandomGradientRun
-- name    : RandomGradFree_Smooth_IsRandomGradientRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T08:39:37.398327+00:00
-- url     : https://prove2.me/theorems/ce89b9f2-901f-4707-9d1d-0769fbc4b259
-- title:
--   A run of the random gradient method $\mathcal{RG}_\mu$ (Eq. (54))
-- statement:
--   Let $E$ be a finite-dimensional real inner product space, $f : E \to \mathbb R$, $\mu \in \mathbb R$ a smoothing parameter, $h$ a step size and $x_0 \in E$ a starting point. Let $(\Omega, \mathcal F, P)$ be a probability space carrying random directions $u_0, u_1, \dots : \Omega \to E$ and iterates $x_0, x_1, \dots : \Omega \to E$. The pair $(u, x)$ is a **run of the random gradient method** $\mathcal{RG}_\mu$ if
--
--   1. the directions $u_k$ are measurable, mutually independent, and each has the standard Gaussian distribution on $E$;
--   2. the first iterate is the deterministic point $x_0$;
--   3. for every $k \ge 0$ and every outcome $\omega$,
--
--   $$
--   x_{k+1} = x_k - h\, B^{-1} g_\mu(x_k),
--   $$
--
--   where the oracle $g_\mu$ of (30) is evaluated at $x_k(\omega)$ in the direction $u_k(\omega)$.
--
--   This is the method whose expected performance Theorem 8 bounds: a gradient step in which the gradient is replaced by a random finite-difference estimate along a Gaussian direction.
--
--   **Formalization Note** Independence is Mathlib's `iIndepFun` and the law is `P.map (u k) = stdGaussian E`; together they say the directions are i.i.d. standard Gaussian. The update is required pointwise for every outcome, so the iterate $x_k$ is a function of $u_0, \dots, u_{k-1}$.
-- source:
--   Nesterov, Spokoiny, Random Gradient-Free Minimization of Convex Functions, Found. Comput. Math. 17 (2017), p. 546, Section 5, Method RG_mu, Eq. (54); p. 541 (i.i.d. directions U_k)

import Mathlib
import Definitions.Def_RandomGradFree_Shared_oracle

namespace RandomGradFree.Smooth

open MeasureTheory ProbabilityTheory

/-- A run of the random gradient method `RG_μ` (Nesterov–Spokoiny, Eq. (54), p. 546) with
constant step `h` on the probability space `(Ω, P)`: the directions `u k` are independent, each
a measurable random vector with the standard Gaussian law on `E`; the method starts at `x₀`;
and for every `k` and every outcome `ω`, `x (k+1) ω = x_k - h B⁻¹ g_μ(x_k)`, where the oracle
is evaluated at the direction `u k ω`. -/
structure IsRandomGradientRun {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f : E → ℝ) (μ : ℝ) (h : ℝ) (x₀ : E)
    (u : ℕ → Ω → E) (x : ℕ → Ω → E) : Prop where
  measurable_dir : ∀ k, Measurable (u k)
  indep_dir : iIndepFun u P
  law_dir : ∀ k, P.map (u k) = stdGaussian E
  init : x 0 = fun _ => x₀
  step : ∀ k ω, x (k + 1) ω = x k ω - h • RandomGradFree.Shared.oracle f μ (x k ω) (u k ω)

end RandomGradFree.Smooth


