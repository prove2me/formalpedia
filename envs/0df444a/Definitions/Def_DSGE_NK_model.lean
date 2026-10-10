-- Prove2me | Definitions.Def_DSGE_NK_model
-- name    : DSGE_NK_model
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-09T21:27:56.508723+00:00
-- url     : https://prove2.me/theorems/6398d62f-3bb6-4795-b3ac-3f5c2e0dffd0
-- title:
--   Three-equation New Keynesian model: equilibrium, boundedness, determinacy
-- statement:
--   This file fixes the **basic three-equation New Keynesian model** in its deterministic (shock-free) form, with all variables written as deviations from the zero-inflation steady state. Time is discrete, $t = 0, 1, 2, \dots$; $y_t$ is the output gap, $\pi_t$ inflation and $i_t$ the nominal interest rate. The real parameters are $\sigma$ (inverse elasticity of intertemporal substitution), $\beta$ (discount factor), $\kappa$ (slope of the Phillips curve), and the Taylor-rule coefficients $\phi_\pi, \phi_y$.
--
--   1. **Equilibrium.** Real sequences $(y_t, \pi_t, i_t)_{t \ge 0}$ form an equilibrium if for every $t \ge 0$
--   $$
--   \begin{aligned}
--   y_t &= y_{t+1} - \tfrac{1}{\sigma}\,(i_t - \pi_{t+1}) &&\text{(demand / dynamic IS curve)}\\
--   \pi_t &= \beta\,\pi_{t+1} + \kappa\, y_t &&\text{(supply / New Keynesian Phillips curve)}\\
--   i_t &= \phi_\pi\, \pi_t + \phi_y\, y_t &&\text{(monetary policy / Taylor rule)}.
--   \end{aligned}
--   $$
--   2. **Bounded sequence.** A real sequence $(x_t)$ is bounded if there is $C$ with $|x_t| \le C$ for all $t$.
--   3. **Determinacy.** The parameter vector is *determinate* if every equilibrium in which $y$, $\pi$ and $i$ are all bounded is identically zero, i.e. the steady state is the unique bounded equilibrium.
--
--   These three blocks (demand, supply, monetary policy) are exactly the simplified DSGE model described in the source; the definitions are shared by every statement of the mission.
--
--   **Formalization Note.** Sequences are functions $\mathbb N \to \mathbb R$. The factor $1/\sigma$ uses Lean's total division, so for $\sigma = 0$ the IS equation degenerates to $y_t = y_{t+1}$; the theorems that use this definition assume $\sigma > 0$ or $\sigma \ne 0$. Expectations operators are absent because the model is deterministic.
-- source:
--   Wikipedia, "Dynamic stochastic general equilibrium" (uploaded PDF), section "DSGE modeling — Structure" (simplified demand / supply / monetary-policy model) and section "Criticism" (consumption Euler equation paragraph); https://en.wikipedia.org/wiki/Dynamic_stochastic_general_equilibrium; equations as in J. Galí, Monetary Policy, Inflation, and the Business Cycle, Princeton University Press, 2008, Chapter 3 (the basic New Keynesian model under an interest-rate rule); J. Bullard and K. Mitra, Learning about monetary policy rules, J. Monetary Economics 49 (2002) 1105-1129

import Mathlib

/-!
# The basic three-equation New Keynesian model (deterministic, shock-free)

All variables are deviations from the zero-inflation steady state:
* `y t` — output gap in period `t`,
* `π t` — inflation in period `t`,
* `i t` — nominal interest rate in period `t`.

Parameters: `σ` (inverse elasticity of intertemporal substitution), `β` (discount factor),
`κ` (slope of the Phillips curve), `φπ`, `φy` (Taylor-rule coefficients).
-/

namespace DSGE

/-- `(y, π, i)` solves the three-equation New Keynesian model in every period `t`:
* demand (dynamic IS curve): `y t = y (t+1) - (1/σ) (i t - π (t+1))`,
* supply (New Keynesian Phillips curve): `π t = β π (t+1) + κ y t`,
* monetary policy (Taylor rule): `i t = φπ π t + φy y t`. -/
def IsNKEquilibrium (σ β κ φπ φy : ℝ) (y π i : ℕ → ℝ) : Prop :=
  ∀ t : ℕ,
    y t = y (t + 1) - (1 / σ) * (i t - π (t + 1)) ∧
    π t = β * π (t + 1) + κ * y t ∧
    i t = φπ * π t + φy * y t

/-- A real sequence is bounded: there is `C` with `|x t| ≤ C` for all `t`. -/
def IsBoundedSeq (x : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, ∀ t : ℕ, |x t| ≤ C

/-- Determinacy: the zero (steady-state) path is the only bounded solution of the model. -/
def IsDeterminate (σ β κ φπ φy : ℝ) : Prop :=
  ∀ y π i : ℕ → ℝ, IsNKEquilibrium σ β κ φπ φy y π i →
    IsBoundedSeq y → IsBoundedSeq π → IsBoundedSeq i →
    ∀ t : ℕ, y t = 0 ∧ π t = 0 ∧ i t = 0

end DSGE


