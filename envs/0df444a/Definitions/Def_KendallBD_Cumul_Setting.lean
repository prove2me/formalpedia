-- Prove2me | Definitions.Def_KendallBD_Cumul_Setting
-- name    : KendallBD_Cumul_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T11:11:52.55544+00:00
-- url     : https://prove2.me/theorems/1f4f2988-9a1e-4f46-b025-781e0dbed1cc
-- title:
--   §5, (49), (50), (52), (53) and §4, (31), pp. 8–11 — the roots α, β, the generating function ψ, x, Q_M and the PDE (31)
-- statement:
--   This file fixes the objects of Kendall's §5, *the asymptotic distribution of the cumulative population for a simple transient birth-and-death process*, in which the birth and death rates are constants $\lambda_0$ and $\mu_0$.
--
--   In a birth-and-death process started from one ancestor ($n_0 = 1$), the **cumulative population** $M_t$ starts at $M_0 = n_0 = 1$ and shares all the positive jumps of the population size $n_t$: it counts every individual ever born, plus the ancestor. The joint generating function $\psi(z, w, t) = \sum_{n, M} P_{n,M}(t) z^n w^M$ of $(n_t, M_t)$ satisfies the first-order partial differential equation (31) with boundary condition (32), $\psi(z, w, 0) = zw$. The paper does not construct the process; it works with the explicit solution of (31)–(32), and so does this file.
--
--   1. **The discriminant** of the quadratic (49), $\lambda_0 w z^2 - (\lambda_0 + \mu_0) z + \mu_0 = 0$ in $z$:
--   $$\operatorname{disc}(w) = (\lambda_0 + \mu_0)^2 - 4\lambda_0\mu_0 w.$$
--   2. **The roots** of (49):
--   $$\alpha = \frac{\lambda_0 + \mu_0 - \sqrt{\operatorname{disc}(w)}}{2\lambda_0 w}, \qquad \beta = \frac{\lambda_0 + \mu_0 + \sqrt{\operatorname{disc}(w)}}{2\lambda_0 w}.$$
--   3. **The generating function** (50):
--   $$\psi(z, w, t) = w\,\frac{\alpha(\beta - z) + \beta(z - \alpha)e^{-\lambda_0 w(\beta - \alpha)t}}{(\beta - z) + (z - \alpha)e^{-\lambda_0 w(\beta - \alpha)t}}.$$
--   4. **The parameter** (53): $x = 4\lambda_0\mu_0/(\lambda_0 + \mu_0)^2$.
--   5. **The law** (52) of $M_\infty$: for $M = 1, 2, 3, \dots$
--   $$Q_M = \frac{\lambda_0 + \mu_0}{2\lambda_0}\,\frac{(2M)!}{2^{2M}(M!)^2}\,\frac{x^M}{2M - 1},$$
--   and $Q_0 = 0$.
--   6. **The equation (31)** with constant rates, at a point $(z, w, t)$: a function $\psi(z, w, t)$ satisfies it there if both partial derivatives $\partial\psi/\partial t$ and $\partial\psi/\partial z$ exist at that point and
--   $$\frac{\partial \psi}{\partial t} = \{\lambda_0 w z^2 - (\lambda_0 + \mu_0) z + \mu_0\}\frac{\partial \psi}{\partial z}.$$
--
--   These are the objects of the mission's goal: $\psi$ of (50) solves (31)–(32), and its value at $z = 1$, $t \to \infty$ generates the law $Q_M$.
--
--   **Formalization Note.** The roots are given by the quadratic formula with $\alpha$ taking the minus sign, as the paper's choice $0 < \alpha < 1 < \beta$ requires; they are meaningful for $\lambda_0 > 0$ and $w \ne 0$, and every theorem uses them only for $0 < w < 1$. $Q_0 = 0$ records that $M_\infty \ge M_0 = 1$; the page lists $Q_M$ only for $M \ge 1$. The factor $(2M)!/(2^{2M}(M!)^2)$ is kept in the printed shape, with $2M - 1$ computed in the reals. The PDE is stated with explicit derivatives (`HasDerivAt`), never with `deriv`, so that it cannot hold through a junk value.
-- source:
--   Kendall, On the generalized "birth-and-death" process, Ann. Math. Statist. 19 (1948), §4, (30)–(32), p. 8; §5, (49), (50), (52), (53), pp. 10–11

import Mathlib

namespace KendallBD.Cumul

/-- The discriminant of the quadratic (49), `λ₀ w z² − (λ₀ + μ₀) z + μ₀ = 0`, in `z`:
`(λ₀ + μ₀)² − 4 λ₀ μ₀ w`. -/
noncomputable def disc (lam0 mu0 w : ℝ) : ℝ :=
  (lam0 + mu0) ^ 2 - 4 * lam0 * mu0 * w

/-- The smaller root `α` of (49): `(λ₀ + μ₀ − √disc) / (2 λ₀ w)`. -/
noncomputable def alpha (lam0 mu0 w : ℝ) : ℝ :=
  (lam0 + mu0 - Real.sqrt (disc lam0 mu0 w)) / (2 * lam0 * w)

/-- The larger root `β` of (49): `(λ₀ + μ₀ + √disc) / (2 λ₀ w)`. -/
noncomputable def beta (lam0 mu0 w : ℝ) : ℝ :=
  (lam0 + mu0 + Real.sqrt (disc lam0 mu0 w)) / (2 * lam0 * w)

/-- Kendall's explicit generating function (50):
`ψ(z, w, t) = w · (α(β − z) + β(z − α) e^{−λ₀ w (β − α) t}) / ((β − z) + (z − α) e^{−λ₀ w (β − α) t})`. -/
noncomputable def psi (lam0 mu0 z w t : ℝ) : ℝ :=
  w * ((alpha lam0 mu0 w * (beta lam0 mu0 w - z)
        + beta lam0 mu0 w * (z - alpha lam0 mu0 w)
          * Real.exp (-lam0 * w * (beta lam0 mu0 w - alpha lam0 mu0 w) * t))
      / ((beta lam0 mu0 w - z)
        + (z - alpha lam0 mu0 w)
          * Real.exp (-lam0 * w * (beta lam0 mu0 w - alpha lam0 mu0 w) * t)))

/-- The parameter (53): `x = 4 λ₀ μ₀ / (λ₀ + μ₀)²`. -/
noncomputable def x (lam0 mu0 : ℝ) : ℝ :=
  4 * lam0 * mu0 / (lam0 + mu0) ^ 2

/-- The law (52) of the cumulative population `M_∞`:
`Q_M = ((λ₀ + μ₀)/(2λ₀)) · ((2M)!/(2^{2M}(M!)²)) · (x^M/(2M − 1))` for `M = 1, 2, 3, …`,
and `Q_0 = 0` (the cumulative population is at least its initial value `M_0 = 1`). -/
noncomputable def Q (lam0 mu0 : ℝ) (M : ℕ) : ℝ :=
  if M = 0 then 0
  else (lam0 + mu0) / (2 * lam0)
    * ((Nat.factorial (2 * M) : ℝ) / (2 ^ (2 * M) * (Nat.factorial M : ℝ) ^ 2))
    * (x lam0 mu0 ^ M / (2 * (M : ℝ) - 1))

/-- The partial differential equation (31) with constant rates `λ₀, μ₀`, at one point `(z, w, t)`:
both partial derivatives of `ψ` exist there (as genuine derivatives) and
`∂ψ/∂t = (λ₀ w z² − (λ₀ + μ₀) z + μ₀) ∂ψ/∂z`. -/
def SolvesPDE (lam0 mu0 : ℝ) (ψ : ℝ → ℝ → ℝ → ℝ) (z w t : ℝ) : Prop :=
  ∃ a b : ℝ, HasDerivAt (fun s => ψ z w s) a t ∧ HasDerivAt (fun y => ψ y w t) b z ∧
    a = (lam0 * w * z ^ 2 - (lam0 + mu0) * z + mu0) * b

end KendallBD.Cumul


