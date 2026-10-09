-- Prove2me | Definitions.Def_ProjReflGrad_Adaptive_Setting
-- name    : ProjReflGrad_Adaptive_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T09:14:37.470124+00:00
-- url     : https://prove2.me/theorems/b2cabb25-5dd4-48e4-a2e2-6e5cab104666
-- title:
--   (1.1), (C1)–(C3), Algorithm 4.2, pp. 1, 8–9 — projection, solution set, monotone and Lipschitz maps, weak convergence, runs of the adaptive projected reflected gradient method
-- statement:
--   Let $H$ be a real inner product space (a real Hilbert space in every theorem that uses these objects), $C \subseteq H$ and $F : H \to H$.
--
--   1. **Nearest point and projection.** A point $p$ is a nearest point of $C$ to $z$ if $p \in C$ and $\|z - p\| \le \|z - q\|$ for all $q \in C$. The metric projection $P_C z$ is such a nearest point. When $C$ is nonempty, closed and convex and $H$ is complete, the nearest point exists and is unique.
--   2. **The variational inequality (1.1) and its solution set.** $S = \{x^* \in C : \langle F(x^*), x - x^* \rangle \ge 0 \text{ for all } x \in C\}$.
--   3. **(C2)** $F$ is monotone on $H$: $\langle F(x) - F(y), x - y\rangle \ge 0$ for all $x, y \in H$. **(C3)** $F$ is $L$-Lipschitz on $H$: $\|F(x) - F(y)\| \le L\|x - y\|$ for all $x, y$ (the theorems add $L > 0$).
--   4. **Weak convergence.** $x_n \rightharpoonup x^*$ means $\langle x_n, v\rangle \to \langle x^*, v\rangle$ for every $v \in H$.
--   5. **The step rule (4.1).** With the convention $0/0 = +\infty$ (hence $a/0 = +\infty$), given the previous reflection $y_{n-1}$, weight $\tau_{n-1}$ and step $\lambda_{n-1}$,
--   $$\lambda(y,\tau) = \min\Big\{\frac{\alpha\|y - y_{n-1}\|}{\|F(y) - F(y_{n-1})\|},\ \frac{1+\tau_{n-1}}{\tau}\lambda_{n-1},\ \bar\lambda\Big\},$$
--   where the first term is omitted when $F(y) = F(y_{n-1})$. The initial step is $\lambda_0 = \min\{\alpha\|x_0 - y_0\|/\|F(x_0) - F(y_0)\|, \bar\lambda\}$, equal to $\bar\lambda$ when $F(x_0) = F(y_0)$.
--   6. **The test quantity.**
--   $$t_n = -\|x_{n+1} - x_n\|^2 + 2\lambda_n\langle F(y_n), y_n - x_{n+1}\rangle + (1 - \alpha(1+\sqrt2))\|x_n - y_n\|^2 - \alpha\|x_n - y_{n-1}\|^2 + (1 - \sqrt2\alpha)\|x_{n+1} - y_n\|^2.$$
--   7. **Runs of Algorithm 4.2.** Sequences $(x_n), (y_n) \subseteq H$, $(\lambda_n), (\tau_n) \subseteq \mathbb R$ form a run with parameters $\alpha$, $\lambda_{-1}$, $\bar\lambda$ when: $x_0 \in C$, $y_0 = P_C(x_0 - \lambda_{-1}F(x_0))$, $\lambda_0$ is the initial step, $\tau_0 = 1$, $x_1 = P_C(x_0 - \lambda_0 F(y_0))$; and for every $n \ge 1$, with the trial values $\hat y_n = 2x_n - x_{n-1}$, $\hat\lambda_n = \lambda(\hat y_n, 1)$, $\hat x_{n+1} = P_C(x_n - \hat\lambda_n F(\hat y_n))$ and $\hat t_n$ the test quantity at these trial values, one of the following holds:
--      - $\hat t_n \le 0$, and the trial is accepted: $y_n = \hat y_n$, $\lambda_n = \hat\lambda_n$, $\tau_n = 1$, $x_{n+1} = \hat x_{n+1}$;
--      - (step 4.i) $\hat t_n > 0$, $\hat\lambda_n \ge \lambda_{n-1}$, $y_n = \hat y_n$, $\tau_n = 1$, $\lambda_n \in [\lambda_{n-1}, \hat\lambda_n]$ satisfies (4.2) $\|\lambda_n F(y_n) - \lambda_{n-1}F(y_{n-1})\| \le \alpha\|y_n - y_{n-1}\|$, and $x_{n+1} = P_C(x_n - \lambda_n F(y_n))$;
--      - (step 4.ii) $\hat t_n > 0$, $\hat\lambda_n < \lambda_{n-1}$, $\tau_n \in (0,1]$, $y_n = x_n + \tau_n(x_n - x_{n-1})$ with (4.3) $\lambda(y_n, \tau_n) \ge \tau_n\lambda_{n-1}$, $\lambda_n \in [\tau_n\lambda_{n-1}, \lambda(y_n,\tau_n)]$ satisfies (4.4) $\|\lambda_n F(y_n) - \tau_n\lambda_{n-1}F(y_{n-1})\| \le \alpha\|y_n - y_{n-1}\|$, and $x_{n+1} = P_C(x_n - \lambda_n F(y_n))$.
--
--   The stored values $y_n, \lambda_n, \tau_n$ are the final ones of iteration $n$, after the corrections of step 4. The algorithm never uses the Lipschitz constant $L$.
--
--   These objects are the setting of every statement of §4 of the paper.
--
--   **Formalization Note** The projection is defined by choice: a nearest point when one exists and the junk value $z$ otherwise; every theorem using it assumes $C$ closed, convex and nonempty in a complete space, where the junk branch is never reached. The convention $0/0 = +\infty$ is encoded by dropping the ratio term from the minimum when its denominator vanishes, never by Lean's $x/0 = 0$. The admissible choices $\lambda'_n$, $\tau'_n$ in step 4 range over all values the algorithm allows; nothing selects a particular one. The stopping rule of step 3 ("if $r(x_n, y_n) = 0$ then stop") is not encoded: if the residual vanishes then $\hat x_{n+1} = x_n = \hat y_n$ and $\hat t_n = -\alpha\|x_n - y_{n-1}\|^2 \le 0$, so the first branch continues a stopped run as a constant sequence.
-- source:
--   Malitsky, Projected Reflected Gradient Methods for Monotone Variational Inequalities, arXiv:1502.04968v1, pp. 1, 8–9, (1.1), (C1)–(C3), (4.1)–(4.4), Algorithm 4.2

import Mathlib
import Definitions.Def_ProjReflGrad_Weak_Setting

namespace ProjReflGrad.Adaptive

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- `λ(y, τ)` of (4.1), relative to the previous data `(y_{n-1}, τ_{n-1}, λ_{n-1}) = (yp, taup, lamp)`:
`min {α‖y - y_{n-1}‖ / ‖F(y) - F(y_{n-1})‖, ((1 + τ_{n-1}) / τ) λ_{n-1}, λ̄}`, with the paper's
convention `0/0 = +∞` (hence `a/0 = +∞`): when `F y = F yp` the ratio term is `+∞` and drops out
of the minimum. -/
noncomputable def stepCap (F : H → H) (α lamBar : ℝ) (yp : H) (taup lamp : ℝ) (y : H) (tau : ℝ) : ℝ := by
  classical
  exact if F y = F yp then min ((1 + taup) / tau * lamp) lamBar
    else min (α * ‖y - yp‖ / ‖F y - F yp‖) (min ((1 + taup) / tau * lamp) lamBar)

/-- `λ₀ = min {α‖x₀ - y₀‖ / ‖F(x₀) - F(y₀)‖, λ̄}` of step 1 of Algorithm 4.2, with the same
convention `0/0 = +∞`: when `F x₀ = F y₀` the ratio term drops out and `λ₀ = λ̄`. -/
noncomputable def initStep (F : H → H) (α lamBar : ℝ) (x0 y0 : H) : ℝ := by
  classical
  exact if F x0 = F y0 then lamBar else min (α * ‖x0 - y0‖ / ‖F x0 - F y0‖) lamBar

/-- The test quantity `t_n` of step 3 of Algorithm 4.2, evaluated at the current point `xn`,
the trial point `xnext`, the trial reflection `yn`, the previous reflection `yprev` and the
trial step `lamn`:
`-‖x_{n+1} - x_n‖² + 2λ_n⟨F(y_n), y_n - x_{n+1}⟩ + (1 - α(1 + √2))‖x_n - y_n‖²
 - α‖x_n - y_{n-1}‖² + (1 - √2 α)‖x_{n+1} - y_n‖²`. -/
noncomputable def tTest (F : H → H) (α : ℝ) (xn xnext yn yprev : H) (lamn : ℝ) : ℝ :=
  -‖xnext - xn‖ ^ 2 + 2 * lamn * inner ℝ (F yn) (yn - xnext)
    + (1 - α * (1 + Real.sqrt 2)) * ‖xn - yn‖ ^ 2
    - α * ‖xn - yprev‖ ^ 2 + (1 - Real.sqrt 2 * α) * ‖xnext - yn‖ ^ 2

/-- `(x, y, lam, tau)` is a run of Algorithm 4.2 with parameters `α`, `λ_{-1} = lamInit` and
`λ̄ = lamBar`. The values `y n`, `lam n`, `tau n` are the final ones of iteration `n`, after the
corrections of step 4. Step 1: `x₀ ∈ C`, `y₀ = P_C(x₀ - λ_{-1}F(x₀))`, `λ₀` as in `initStep`,
`τ₀ = 1`, `x₁ = P_C(x₀ - λ₀F(y₀))`. For `n ≥ 1`, step 2 forms the trial reflection
`ŷ = 2x_n - x_{n-1}`, the trial step `λ̂ = λ(ŷ, 1)` and the trial point `x̂ = P_C(x_n - λ̂F(ŷ))`,
and step 3 the test `t̂ = t_n`; then exactly as in step 4 either `t̂ ≤ 0` and the trial is
accepted, or `t̂ > 0` and branch (i) (`λ̂ ≥ λ_{n-1}`) or branch (ii) (`λ̂ < λ_{n-1}`) makes an
admissible correction. The choices `λ'_n`, `τ'_n` range over all admissible values. -/
def IsAdaptiveRun (C : Set H) (F : H → H) (α lamInit lamBar : ℝ) (x y : ℕ → H) (lam tau : ℕ → ℝ) :
    Prop :=
  x 0 ∈ C ∧ y 0 = ProjReflGrad.Weak.proj C (x 0 - lamInit • F (x 0)) ∧ lam 0 = initStep F α lamBar (x 0) (y 0) ∧
  tau 0 = 1 ∧ x 1 = ProjReflGrad.Weak.proj C (x 0 - lam 0 • F (y 0)) ∧
  ∀ n : ℕ, 1 ≤ n →
    let yh := (2 : ℝ) • x n - x (n - 1)
    let lh := stepCap F α lamBar (y (n - 1)) (tau (n - 1)) (lam (n - 1)) yh 1
    let xh := ProjReflGrad.Weak.proj C (x n - lh • F yh)
    let th := tTest F α (x n) xh yh (y (n - 1)) lh
    -- step 4, `t_n ≤ 0`: accept the trial
    (th ≤ 0 ∧ y n = yh ∧ lam n = lh ∧ tau n = 1 ∧ x (n + 1) = xh) ∨
    -- step 4 (i)
    (0 < th ∧ lam (n - 1) ≤ lh ∧ y n = yh ∧ tau n = 1 ∧ lam n ∈ Set.Icc (lam (n - 1)) lh ∧
      ‖lam n • F (y n) - lam (n - 1) • F (y (n - 1))‖ ≤ α * ‖y n - y (n - 1)‖ ∧
      x (n + 1) = ProjReflGrad.Weak.proj C (x n - lam n • F (y n))) ∨
    -- step 4 (ii)
    (0 < th ∧ lh < lam (n - 1) ∧ tau n ∈ Set.Ioc 0 1 ∧ y n = x n + tau n • (x n - x (n - 1)) ∧
      tau n * lam (n - 1) ≤
        stepCap F α lamBar (y (n - 1)) (tau (n - 1)) (lam (n - 1)) (y n) (tau n) ∧
      lam n ∈ Set.Icc (tau n * lam (n - 1))
        (stepCap F α lamBar (y (n - 1)) (tau (n - 1)) (lam (n - 1)) (y n) (tau n)) ∧
      ‖lam n • F (y n) - (tau n * lam (n - 1)) • F (y (n - 1))‖ ≤ α * ‖y n - y (n - 1)‖ ∧
      x (n + 1) = ProjReflGrad.Weak.proj C (x n - lam n • F (y n)))

end ProjReflGrad.Adaptive


