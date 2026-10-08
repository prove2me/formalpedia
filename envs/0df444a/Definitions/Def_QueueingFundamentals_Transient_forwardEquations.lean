-- Prove2me | Definitions.Def_QueueingFundamentals_Transient_forwardEquations
-- name    : QueueingFundamentals_Transient_forwardEquations
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T07:32:26.878727+00:00
-- url     : https://prove2.me/theorems/1a1e89ed-3bc4-491b-8996-c030d74734a6
-- title:
--   Forward (differential–difference) equations of M/M/1/1, M/M/1, M/M/∞ and the M/M/1 busy period
-- statement:
--   This file fixes the four systems of differential–difference equations of §§2.11–2.12 and what it means to solve them.
--
--   1. **M/M/1/1**, equations (2.70): for the state probabilities $(p_0(t), p_1(t))$,
--   $$ p_1'(t) = -\mu p_1(t) + \lambda p_0(t), \qquad p_0'(t) = -\lambda p_0(t) + \mu p_1(t). $$
--   2. **M/M/1**, equations (2.72): for $n \ge 0$,
--   $$ p_n'(t) = -(\lambda+\mu) p_n(t) + \lambda p_{n-1}(t) + \mu p_{n+1}(t)\ (n>0), \qquad p_0'(t) = -\lambda p_0(t) + \mu p_1(t). $$
--   3. **M/M/∞**, equations (2.76): with $\lambda_n = \lambda$ and $\mu_n = n\mu$,
--   $$ p_n'(t) = -(\lambda+n\mu) p_n(t) + \lambda p_{n-1}(t) + (n+1)\mu p_{n+1}(t)\ (n>0), \qquad p_0'(t) = -\lambda p_0(t) + \mu p_1(t). $$
--   4. **M/M/1 with an absorbing barrier at 0** ($\lambda_0 = 0$), the busy-period equations of §2.12:
--   $$ p_0'(t) = \mu p_1(t), \quad p_1'(t) = -(\lambda+\mu)p_1(t) + \mu p_2(t), \quad p_n'(t) = -(\lambda+\mu)p_n(t) + \lambda p_{n-1}(t) + \mu p_{n+1}(t)\ (n \ge 2). $$
--
--   A family $(p_n)_n$ of real functions **solves** such a system on $[0,\infty)$ if, for every state $n$ and every $t \ge 0$, $p_n$ is differentiable at $t$ relative to $[0,\infty)$ (an ordinary derivative for $t>0$, a right derivative at $t=0$) with derivative given by the right-hand side. The family is a **probability family** if for every $t \ge 0$ the numbers $p_n(t)$ are nonnegative and sum to $1$.
--
--   These are the objects about which the transient results of the chapter are stated; the probability-family condition is the class in which the transient solutions are unique.
--
--   **Formalization Note** The state space is `Fin 2` for M/M/1/1 and `ℕ` otherwise; each right-hand side is a function of the current state vector. Solutions use `HasDerivWithinAt` on `Set.Ici 0`; the probability condition uses `HasSum`.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.97 Eq. (2.70), p.99 Eq. (2.72), p.101 Eq. (2.76), p.102 busy-period equations (§2.12)

import Mathlib

namespace QueueingFundamentals.Transient

/-- Right-hand side of the M/M/1/1 equations (2.70), for the state `p = (p₀, p₁)`:
`p₀' = -λ p₀ + μ p₁`, `p₁' = -μ p₁ + λ p₀`. -/
def mm11RHS (lam mu : ℝ) (p : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun k => if k = 0 then -lam * p 0 + mu * p 1 else -mu * p 1 + lam * p 0

/-- Right-hand side of the M/M/1 forward equations (2.72):
`p₀' = -λ p₀ + μ p₁` and `p_n' = -(λ+μ) p_n + λ p_{n-1} + μ p_{n+1}` for `n > 0`. -/
def mm1RHS (lam mu : ℝ) (p : ℕ → ℝ) : ℕ → ℝ
  | 0 => -lam * p 0 + mu * p 1
  | n + 1 => -(lam + mu) * p (n + 1) + lam * p n + mu * p (n + 2)

/-- Right-hand side of the M/M/∞ forward equations (2.76), with `λ_n = λ`, `μ_n = nμ`:
`p₀' = -λ p₀ + μ p₁` and `p_n' = -(λ + nμ) p_n + λ p_{n-1} + (n+1)μ p_{n+1}` for `n > 0`. -/
def mmInfRHS (lam mu : ℝ) (p : ℕ → ℝ) : ℕ → ℝ
  | 0 => -lam * p 0 + mu * p 1
  | n + 1 => -(lam + ((n : ℝ) + 1) * mu) * p (n + 1) + lam * p n + ((n : ℝ) + 2) * mu * p (n + 2)

/-- Right-hand side of the busy-period equations of §2.12 (p.102): the M/M/1 equations with an
absorbing barrier at `0` (`λ₀ = 0`): `p₀' = μ p₁`, `p₁' = -(λ+μ) p₁ + μ p₂`, and
`p_n' = -(λ+μ) p_n + λ p_{n-1} + μ p_{n+1}` for `n ≥ 2`. -/
def busyRHS (lam mu : ℝ) (p : ℕ → ℝ) : ℕ → ℝ
  | 0 => mu * p 1
  | 1 => -(lam + mu) * p 1 + mu * p 2
  | n + 2 => -(lam + mu) * p (n + 2) + lam * p (n + 1) + mu * p (n + 3)

/-- `p` solves the differential–difference system with right-hand side `F` on `[0, ∞)`: for every
state `n` and every `t ≥ 0`, `p_n` has derivative `F(p(t))_n` at `t` within `[0, ∞)` (an ordinary
derivative for `t > 0`, the right derivative at `t = 0`). -/
def IsForwardSolution {S : Type*} (F : (S → ℝ) → S → ℝ) (p : S → ℝ → ℝ) : Prop :=
  ∀ n : S, ∀ t : ℝ, 0 ≤ t →
    HasDerivWithinAt (p n) (F (fun m => p m t) n) (Set.Ici (0 : ℝ)) t

/-- `p(t)` is a probability distribution on the states for every `t ≥ 0`:
`p_n(t) ≥ 0` and `∑_n p_n(t) = 1`. This is the class in which the transient solutions are
unique. -/
def IsProbabilityFamily {S : Type*} (p : S → ℝ → ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → (∀ n : S, 0 ≤ p n t) ∧ HasSum (fun n => p n t) 1

end QueueingFundamentals.Transient


