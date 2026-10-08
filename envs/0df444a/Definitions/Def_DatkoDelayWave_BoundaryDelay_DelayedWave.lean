-- Prove2me | Definitions.Def_DatkoDelayWave_BoundaryDelay_DelayedWave
-- name    : DatkoDelayWave_BoundaryDelay_DelayedWave
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T02:41:49.822833+00:00
-- url     : https://prove2.me/theorems/09610480-ec0d-4568-81e5-7d2f50239f1d
-- title:
--   The delayed boundary-feedback system (1), (2), (8), the functions f and h of (9), and the spectrum of the eigenvalue problem (p. 154)
-- statement:
--   This file sets up the model of Datko, Lagnese and Polis (1986). Throughout, $a \ge 0$ is the damping coefficient, $k \ge 0$ the feedback gain and $\varepsilon$ the time delay (the paper takes $\varepsilon > 0$), all real.
--
--   1. **The constant $K$.** $K = e^{-2a}$, a number in $(0, 1]$, with $K < 1$ exactly when $a > 0$. The critical gain of the paper is $(1 - K)/(1 + K)$.
--
--   2. **The functions $f$ and $h$ of (9).** For $\omega \in \mathbb C$,
--   $$
--   f(\varepsilon,\omega) = 1 + K e^{-2\omega} + k e^{-\varepsilon\omega}\bigl(1 - K e^{-2\omega}\bigr),\qquad
--   h(\varepsilon,\omega) = \omega f(\varepsilon,\omega) + a\bigl(1 + K e^{-2\omega}\bigr).
--   $$
--   Both are entire functions of $\omega$; they depend on $a$ and $k$ as well.
--
--   3. **Classical solutions of the delayed system.** A function $u(x,t)$ of two real variables with complex values is a classical solution of (1), (2), (8) if it is twice continuously differentiable on $\mathbb R^2$ and
--   $$
--   \begin{aligned}
--   &(1)\quad u_{tt} - u_{xx} + 2a u_t + a^2 u = 0, && 0 < x < 1,\ t > 0,\\
--   &(2)\quad u(0,t) = 0, && t > 0,\\
--   &(8)\quad u_x(1,t) = -k\,u_t(1, t - \varepsilon), && t > \varepsilon.
--   \end{aligned}
--   $$
--   The values of $u$ for $t \le \varepsilon$ play the role of initial data and history.
--
--   4. **Eigenpairs and the spectrum.** A function $\varphi : \mathbb R \to \mathbb C$ is an eigenfunction for $\omega \in \mathbb C$ if it is $C^2$ and
--   $$
--   \varphi''(x) = (a + \omega)^2 \varphi(x)\ \ (0 < x < 1),\qquad \varphi(0) = 0,\qquad \varphi'(1) + k\omega e^{-\varepsilon\omega}\varphi(1) = 0 .
--   $$
--   The **spectrum** $\sigma(a,k,\varepsilon)$ of (1), (2), (8) is the set of $\omega$ that admit an eigenfunction not identically zero on $[0,1]$. At $\varepsilon = 0$ this is the spectrum of the undelayed problem (5), (6).
--
--   5. **Exponentially unstable solutions.** A classical solution $u$ is exponentially unstable if there are $\gamma > 0$, $c > 0$ and $x_0 \in (0,1)$ with $|u(x_0,t)| \ge c e^{\gamma t}$ for all $t \ge 0$.
--
--   6. **Sets of delays.** A set $R$ is *countably dense in $(0,\infty)$* if $R \subseteq (0,\infty)$, $R$ is countable and every point of $(0,\infty)$ lies in the closure of $R$. A set $D$ is *open and dense in $(0,\infty)$* if $D \subseteq (0,\infty)$ is open and every point of $(0,\infty)$ lies in its closure.
--
--   These are the objects of the paper's THEOREM and of its two lemmas.
--
--   **Formalization Note** Solutions and eigenfunctions are complex-valued, as in the paper's ansatz $u = e^{\omega t}\varphi(x)$; partial derivatives are derivatives of the one-variable sections. Regularity is imposed globally ($C^2$ on $\mathbb R^2$, resp. on $\mathbb R$), which loses no eigenvalue because every solution of (5) on $[0,1]$ is a combination of $e^{\pm(a+\omega)x}$ and extends to $\mathbb R$. The spectrum is defined by the eigenvalue problem, not as the zero set of $h$: $h(\varepsilon,-a) = 0$ always, but $-a$ is an eigenvalue only when $1 = k a e^{\varepsilon a}$. "Exponentially unstable" is read pointwise; the paper does not define it.
-- source:
--   Datko, Lagnese, Polis, An example on the effect of time delays in boundary feedback stabilization of wave equations, SIAM J. Control Optim. 24 (1986), pp. 152–154, Eqs. (1), (2), (5), (6), (8), (9), THEOREM, and the eigenvalue problem in the proof of the Theorem (p. 154)

import Mathlib

namespace DatkoDelayWave.BoundaryDelay

/-- The constant `K = e^{-2a}` of the THEOREM (p. 153). -/
noncomputable def K (a : ℝ) : ℝ := Real.exp (-2 * a)

/-- The function `f(ε, ω) = 1 + K e^{-2ω} + k e^{-εω}(1 - K e^{-2ω})` of (9), p. 153,
with the damping `a` (through `K = e^{-2a}`) and the gain `k` as explicit arguments. -/
noncomputable def f (a k ε : ℝ) (ω : ℂ) : ℂ :=
  1 + (K a : ℂ) * Complex.exp (-2 * ω)
    + (k : ℂ) * Complex.exp (-(ε : ℂ) * ω) * (1 - (K a : ℂ) * Complex.exp (-2 * ω))

/-- The function `h(ε, ω) = ω f(ε, ω) + a(1 + K e^{-2ω})` of (9), p. 153. -/
noncomputable def h (a k ε : ℝ) (ω : ℂ) : ℂ :=
  ω * f a k ε ω + (a : ℂ) * (1 + (K a : ℂ) * Complex.exp (-2 * ω))

/-- Time derivative `u_t(x, t)` of `u : ℝ → ℝ → ℂ` (space variable first). -/
noncomputable def ut (u : ℝ → ℝ → ℂ) (x t : ℝ) : ℂ := deriv (fun s => u x s) t

/-- Second time derivative `u_tt(x, t)`. -/
noncomputable def utt (u : ℝ → ℝ → ℂ) (x t : ℝ) : ℂ := deriv (fun s => ut u x s) t

/-- Space derivative `u_x(x, t)`. -/
noncomputable def ux (u : ℝ → ℝ → ℂ) (x t : ℝ) : ℂ := deriv (fun y => u y t) x

/-- Second space derivative `u_xx(x, t)`. -/
noncomputable def uxx (u : ℝ → ℝ → ℂ) (x t : ℝ) : ℂ := deriv (fun y => ux u y t) x

/-- A classical (complex-valued) solution of the delayed system (1), (2), (8), pp. 152–153,
with damping `a`, gain `k` and delay `ε`:
`u` is `C²` on `ℝ × ℝ` and
(1) `u_tt - u_xx + 2a u_t + a² u = 0` for `0 < x < 1`, `t > 0`;
(2) `u(0, t) = 0` for `t > 0`;
(8) `u_x(1, t) = -k u_t(1, t - ε)` for `t > ε`.
The values of `u` for `t ≤ ε` play the role of initial data and history. -/
structure IsClassicalSolution (a k ε : ℝ) (u : ℝ → ℝ → ℂ) : Prop where
  contDiff : ContDiff ℝ 2 (fun p : ℝ × ℝ => u p.1 p.2)
  /-- (1) -/
  wave : ∀ x ∈ Set.Ioo (0 : ℝ) 1, ∀ t > 0,
    utt u x t - uxx u x t + 2 * (a : ℂ) * ut u x t + (a : ℂ) ^ 2 * u x t = 0
  /-- (2) -/
  dirichlet : ∀ t > 0, u 0 t = 0
  /-- (8) -/
  delayedFeedback : ∀ t > ε, ux u 1 t = -(k : ℂ) * ut u 1 (t - ε)

/-- `φ` solves the eigenvalue problem of the proof of the Theorem (p. 154) for the value `ω`:
`φ` is `C²`, (5) `φ''(x) = (a + ω)² φ(x)` for `0 < x < 1`, `φ(0) = 0` and
`φ'(1) + k ω e^{-εω} φ(1) = 0`. (Nontriviality is imposed in `delaySpectrum`.) -/
structure IsEigenpair (a k ε : ℝ) (ω : ℂ) (φ : ℝ → ℂ) : Prop where
  contDiff : ContDiff ℝ 2 φ
  /-- (5) -/
  ode : ∀ x ∈ Set.Ioo (0 : ℝ) 1, deriv (deriv φ) x = ((a : ℂ) + ω) ^ 2 * φ x
  left : φ 0 = 0
  right : deriv φ 1 + (k : ℂ) * ω * Complex.exp (-(ε : ℂ) * ω) * φ 1 = 0

/-- The spectrum `σ(a, k, ε)` of (1), (2), (8): the set of `ω ∈ ℂ` admitting an eigenfunction
`φ` that does not vanish identically on `[0, 1]` (proof of the Theorem, p. 154). At `ε = 0`
this is the spectrum of the undelayed problem (5), (6) of p. 153. -/
def delaySpectrum (a k ε : ℝ) : Set ℂ :=
  {ω | ∃ φ : ℝ → ℂ, IsEigenpair a k ε ω φ ∧ ∃ x ∈ Set.Icc (0 : ℝ) 1, φ x ≠ 0}

/-- An exponentially unstable solution of (1), (2), (8) (THEOREM (iii), p. 153): a classical
solution together with a rate `γ > 0`, a constant `c > 0` and a point `x₀ ∈ (0, 1)` such that
`|u(x₀, t)| ≥ c e^{γ t}` for every `t ≥ 0`. -/
def IsExpUnstableSolution (a k ε : ℝ) (u : ℝ → ℝ → ℂ) : Prop :=
  IsClassicalSolution a k ε u ∧
    ∃ γ > (0 : ℝ), ∃ c > (0 : ℝ), ∃ x₀ ∈ Set.Ioo (0 : ℝ) 1,
      ∀ t ≥ (0 : ℝ), c * Real.exp (γ * t) ≤ ‖u x₀ t‖

/-- "A countably dense set `R` in `(0, ∞)`": `R ⊆ (0, ∞)` is countable and dense in `(0, ∞)`. -/
def IsCountablyDenseInPos (R : Set ℝ) : Prop :=
  R ⊆ Set.Ioi 0 ∧ R.Countable ∧ Set.Ioi (0 : ℝ) ⊆ closure R

/-- "A dense open set `D` in `(0, ∞)`": `D ⊆ (0, ∞)` is open and dense in `(0, ∞)`. -/
def IsOpenDenseInPos (D : Set ℝ) : Prop :=
  IsOpen D ∧ D ⊆ Set.Ioi 0 ∧ Set.Ioi (0 : ℝ) ⊆ closure D

end DatkoDelayWave.BoundaryDelay


