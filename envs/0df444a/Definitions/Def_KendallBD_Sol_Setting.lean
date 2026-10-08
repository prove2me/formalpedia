-- Prove2me | Definitions.Def_KendallBD_Sol_Setting
-- name    : KendallBD_Sol_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T11:10:13.217984+00:00
-- url     : https://prove2.me/theorems/d417fd2a-ed42-416a-af5a-579827539742
-- title:
--   §2, (2)–(4), (8)–(12), pp. 2–4 — Kendall’s rate model and explicit distribution
-- statement:
--   Let $\lambda(t)$ and $\mu(t)$ be birth and death rates per individual. Define $\rho(t)$ and $W(t)$ by
--   $$
--   \rho(t)=\int_0^t(\mu(\tau)-\lambda(\tau))\,d\tau,\qquad
--   W(t)=e^{-\rho(t)}\left(1+\int_0^t e^{\rho(\tau)}\mu(\tau)\,d\tau\right).
--   $$
--   Put $\xi_t=1-e^{-\rho(t)}/W(t)$ and $\eta_t=1-1/W(t)$. The one-ancestor population law is $P_0(t)=\xi_t$ and, for $n\ge1$,
--   $$
--   P_n(t)=(1-\xi_t)(1-\eta_t)\eta_t^{n-1}.
--   $$
--   The module also names the corresponding rational generating function, the initial condition $P_1(0)=1$, the forward equations, and the integral $J(t)=\int_0^t e^{\rho(\tau)}\mu(\tau)\,d\tau$ used in the extinction criterion. These definitions fix one shared interpretation for all results in the mission.
--
--   **Formalization Note** The integrals are oriented integrals from $0$ to $t$. The forward equations use two-sided derivatives at nonnegative times and the real coefficient $n-1$ for $n\ge1$.
-- source:
--   Kendall, On the generalized "birth-and-death" process, Ann. Math. Statist. 19 (1948), §2, (2)–(4), (8)–(12), pp. 2–4; §3, (18)–(19), p. 6

import Mathlib

namespace KendallBD.Sol

/-- Kendall's integrated excess death rate, equation (11). -/
noncomputable def rho (lam mu : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ τ in (0 : ℝ)..t, (mu τ - lam τ)

/-- The integrating-factor solution in equation (10a). -/
noncomputable def W (lam mu : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-rho lam mu t) *
    (1 + ∫ τ in (0 : ℝ)..t, Real.exp (rho lam mu τ) * mu τ)

/-- The integral in the extinction criterion (18)–(19). -/
noncomputable def J (lam mu : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ τ in (0 : ℝ)..t, Real.exp (rho lam mu τ) * mu τ

/-- The modified zero mass in equation (12). -/
noncomputable def xi (lam mu : ℝ → ℝ) (t : ℝ) : ℝ :=
  1 - Real.exp (-rho lam mu t) / W lam mu t

/-- The geometric ratio in equation (12). -/
noncomputable def eta (lam mu : ℝ → ℝ) (t : ℝ) : ℝ :=
  1 - 1 / W lam mu t

/-- Kendall's one-ancestor distribution, equation (8). -/
noncomputable def P (lam mu : ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  if n = 0 then xi lam mu t else
    (1 - xi lam mu t) * (1 - eta lam mu t) * eta lam mu t ^ (n - 1)

/-- The rational generating function in equation (9). -/
noncomputable def genFun (ξ η z : ℝ) : ℝ :=
  (ξ + (1 - ξ - η) * z) / (1 - η * z)

/-- One ancestor at time zero, equation (2). -/
def InitialCondition (Q : ℕ → ℝ → ℝ) : Prop :=
  Q 1 0 = 1 ∧ ∀ n, n ≠ 1 → Q n 0 = 0

/-- The forward equations (3)–(4), on nonnegative time. -/
def SolvesForward (lam mu : ℝ → ℝ) (Q : ℕ → ℝ → ℝ) : Prop :=
  (∀ t, 0 ≤ t → HasDerivAt (fun s => Q 0 s) (mu t * Q 1 t) t) ∧
  ∀ n : ℕ, 1 ≤ n → ∀ t, 0 ≤ t →
    HasDerivAt (fun s => Q n s)
      (((n : ℝ) + 1) * mu t * Q (n + 1) t +
        ((n : ℝ) - 1) * lam t * Q (n - 1) t -
        (n : ℝ) * (lam t + mu t) * Q n t) t

end KendallBD.Sol


