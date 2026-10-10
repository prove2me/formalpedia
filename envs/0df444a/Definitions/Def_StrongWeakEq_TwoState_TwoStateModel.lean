-- Prove2me | Definitions.Def_StrongWeakEq_TwoState_TwoStateModel
-- name    : StrongWeakEq_TwoState_TwoStateModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T23:31:57.300083+00:00
-- url     : https://prove2.me/theorems/7a0bede8-312a-47a9-a9a2-f501779e21f7
-- title:
--   §4, p. 11, (4.1)–(4.2) — the two-state generator Q ∼ (a, b) and pseudo-exponential discounting
-- statement:
--   Take $S=\{1,2\}$ and no constraint on the generator ($D_i=E_i$). Every generator is then of the form
--   $$
--   Q=\begin{bmatrix}-a & a\\ b & -b\end{bmatrix},\qquad a,b\ge0, \tag{4.1}
--   $$
--   written $Q\sim(a,b)$. The **pseudo-exponential discount function** is
--   $$
--   \delta(t)=\lambda e^{-\rho t}+(1-\lambda)e^{-\rho' t},\qquad t\ge0, \tag{4.2}
--   $$
--   with constants $\lambda\in(0,1)$ and $\rho,\rho'$; its derivative is $\delta'(t)=-\rho\lambda e^{-\rho t}-\rho'(1-\lambda)e^{-\rho' t}$. Given functions $g_1,g_2$, the payoff is
--   $$
--   f(t,1,(-a,a))=\delta(t)\,g_1(a),\qquad f(t,2,(b,-b))=\delta(t)\,g_2(b),
--   $$
--   and its time derivative $f_t$ is the same expression with $\delta'$ in place of $\delta$.
--
--   This is the model of §4, in which weak and strong equilibria can be computed explicitly.
--
--   **Formalization Note** State 1 of the paper is `0 : Fin 2`, state 2 is `1 : Fin 2`. The payoff is defined for every row $q$: in state 1 it reads the rate $a$ from the entry $q_2$ (`q 1`), in state 2 the rate $b$ from the entry $q_1$ (`q 0`); on rows of $E_1$, $E_2$ this is exactly the paper's $f$. The constants $\lambda,\rho,\rho'$ are free parameters here; their ranges are hypotheses of the theorems that use them.
-- source:
--   Huang & Zhou, Strong and Weak Equilibria for Time-Inconsistent Stochastic Control in Continuous Time, arXiv:1809.09243v3, p. 11, §4, (4.1), (4.2)

import Mathlib

namespace StrongWeakEq.TwoState

/-- (4.1), p. 11: the two-state generator `Q ∼ (a, b)`, `Q = [[−a, a], [b, −b]]`.
State 1 of the paper is `0 : Fin 2`, state 2 is `1 : Fin 2`. -/
def gen (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-a, a; b, -b]

/-- (4.2), p. 11: the pseudo-exponential discount function
`δ(t) = λ e^{−ρ t} + (1 − λ) e^{−ρ' t}`. -/
noncomputable def discount (lam ρ ρ' t : ℝ) : ℝ :=
  lam * Real.exp (-ρ * t) + (1 - lam) * Real.exp (-ρ' * t)

/-- The derivative `δ'(t) = −ρ λ e^{−ρ t} − ρ' (1 − λ) e^{−ρ' t}` of (4.2). -/
noncomputable def discountDeriv (lam ρ ρ' t : ℝ) : ℝ :=
  -ρ * lam * Real.exp (-ρ * t) - ρ' * (1 - lam) * Real.exp (-ρ' * t)

/-- p. 11: the StrongWeakEq.Existence.payoff `f(t, 1, (−a, a)) = δ(t) g₁(a)`, `f(t, 2, (b, −b)) = δ(t) g₂(b)`:
in state 1 (`0 : Fin 2`) the rate `a` is the entry `q 1`; in state 2 (`1 : Fin 2`) the rate `b`
is the entry `q 0`. -/
noncomputable def twoStatePayoff (lam ρ ρ' : ℝ) (g₁ g₂ : ℝ → ℝ) :
    ℝ → Fin 2 → (Fin 2 → ℝ) → ℝ :=
  fun t i q => discount lam ρ ρ' t * (if i = 0 then g₁ (q 1) else g₂ (q 0))

/-- The time derivative `f_t(t, i, q)` of `twoStatePayoff`: the same with `δ'` in place of `δ`. -/
noncomputable def twoStatePayoffDeriv (lam ρ ρ' : ℝ) (g₁ g₂ : ℝ → ℝ) :
    ℝ → Fin 2 → (Fin 2 → ℝ) → ℝ :=
  fun t i q => discountDeriv lam ρ ρ' t * (if i = 0 then g₁ (q 1) else g₂ (q 0))

end StrongWeakEq.TwoState


