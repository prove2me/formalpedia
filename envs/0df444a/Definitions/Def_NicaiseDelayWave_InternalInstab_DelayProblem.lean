-- Prove2me | Definitions.Def_NicaiseDelayWave_InternalInstab_DelayProblem
-- name    : NicaiseDelayWave_InternalInstab_DelayProblem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T21:40:40.592264+00:00
-- url     : https://prove2.me/theorems/42fac9eb-450a-4457-bd59-89628de3c21d
-- title:
--   Classical solutions of the internally damped wave equation with delay (1.12)–(1.14), a ≡ 1
-- statement:
--   Let $(\Omega, \Gamma_D, \Gamma_N)$ be a mixed domain, $\mu_1, \mu_2 \in \mathbb R$ and $\tau \in \mathbb R$ (the delay). A function $u : \mathbb R^n \times \mathbb R \to \mathbb C$ is a **classical solution** of the wave equation with delayed internal damping and $a \equiv 1$ (system (5.20) of Nicaise–Pignotti, i.e. (1.12)–(1.14) with $a \equiv 1$) if
--
--   1. $u$ is $C^2$ on $\Omega \times \mathbb R$ and $C^1$ on $\overline\Omega \times \mathbb R$ (as a function of $(x,t)$);
--   2. for every $x \in \Omega$ and $t > 0$,
--   $$u_{tt}(x,t) - \Delta u(x,t) + \mu_1 u_t(x,t) + \mu_2 u_t(x, t-\tau) = 0;$$
--   3. $u(x,t) = 0$ for $x \in \Gamma_D$ and $t > 0$;
--   4. $\dfrac{\partial u}{\partial \nu}(x,t) = 0$ for $x \in \Gamma_N$ and $t > 0$.
--
--   The values of $u$ at $t = 0$ and on $(-\tau, 0)$ play the role of the initial data (1.15) and the history (1.16): $u_0 = u(\cdot, 0)$, $u_1 = u_t(\cdot, 0)$, $g_0 = u_t$ on $\Omega \times (-\tau, 0)$.
--
--   This is the solution class in which the instability examples of Theorem 1.4 are constructed.
--
--   **Formalization Note** The damping coefficient is fixed to $a \equiv 1$, the only case §5.2 treats ("We restrict our analysis to the case $a(x) \equiv 1$ in $\Omega$"); $a \equiv 1$ satisfies the paper's (1.17)–(1.18) with $\omega = \Omega$. A solution is one function defined for all times, and the initial data and history are its traces, so only data that are traces of one such function are covered. Solutions are complex valued, like the paper's $e^{\lambda t}\varphi(x)$. Regularity is required only up to $C^1$ on the closure, since eigenfunctions of mixed Dirichlet–Neumann problems need not be $C^2$ up to the boundary; the Neumann condition uses the derivative within $\overline\Omega$.
-- source:
--   Nicaise, Pignotti, Stability and Instability Results of the Wave Equation with a Delay Term in the Boundary or Internal Feedbacks, SIAM J. Control Optim. 45 (2006), p. 1563, (1.12)–(1.16); p. 1583, (5.20) and "We restrict our analysis to the case a(x) ≡ 1 in Ω"

import Mathlib
import Definitions.Def_NicaiseDelayWave_InternalInstab_WaveCalculus

namespace NicaiseDelayWave.InternalInstab

/-- `u : ℝⁿ → ℝ → ℂ` is a classical solution of the internally damped wave equation with delay
(Nicaise–Pignotti (1.12)–(1.14) with `a ≡ 1`, i.e. system (5.20)):
* `u` is `C²` on `Ω × ℝ` and `C¹` on `Ω̄ × ℝ` (as a function of `(x, t)`);
* `u_tt(x, t) − Δu(x, t) + μ₁ u_t(x, t) + μ₂ u_t(x, t − τ) = 0` for `x ∈ Ω`, `t > 0`;
* `u(x, t) = 0` for `x ∈ Γ_D`, `t > 0`;
* `∂u/∂ν(x, t) = 0` for `x ∈ Γ_N`, `t > 0`.
The values of `u` for `t ≤ 0` are the initial data (1.15) and the history (1.16). -/
def IsClassicalSolution {n : ℕ} (D : NicaiseDelayWave.Shared.MixedDomain n) (μ₁ μ₂ τ : ℝ)
    (u : EuclideanSpace ℝ (Fin n) → ℝ → ℂ) : Prop :=
  ContDiffOn ℝ 2 (fun p : EuclideanSpace ℝ (Fin n) × ℝ => u p.1 p.2) (D.Ω ×ˢ Set.univ) ∧
  ContDiffOn ℝ 1 (fun p : EuclideanSpace ℝ (Fin n) × ℝ => u p.1 p.2)
    (closure D.Ω ×ˢ Set.univ) ∧
  (∀ x ∈ D.Ω, ∀ t : ℝ, 0 < t →
    utt u x t - laplacianX u x t + ((μ₁ : ℂ) * ut u x t + (μ₂ : ℂ) * ut u x (t - τ)) = 0) ∧
  (∀ x ∈ D.ΓD, ∀ t : ℝ, 0 < t → u x t = 0) ∧
  (∀ x ∈ D.ΓN, ∀ t : ℝ, 0 < t → normalDeriv D (fun y => u y t) x = 0)

end NicaiseDelayWave.InternalInstab


