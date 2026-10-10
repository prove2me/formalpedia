-- Prove2me | Definitions.Def_StrongWeakEq_TwoState_Example43
-- name    : StrongWeakEq_TwoState_Example43
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T23:34:08.762434+00:00
-- url     : https://prove2.me/theorems/de68f7ce-95aa-410a-98b9-f33c41b6a3ca
-- title:
--   Example 4.3, p. 13 — λ = 1/2, ρ = 1, ρ′ = 2, g₁(a) = −a², the piecewise g₂, and Q* ∼ (5/12, 7/12)
-- statement:
--   The data of Example 4.3: in the two-state model with pseudo-exponential discounting take $\lambda=\tfrac12$, $\rho=1$, $\rho'=2$, $g_1(a)=-a^2$ and
--   $$
--   g_2(b)=\begin{cases}\dfrac{193}{144}+\dfrac56\,b, & b<\dfrac7{12},\\[4pt] 2-(1-b)^2, & b\ge\dfrac7{12}.\end{cases}
--   $$
--   The function $g_2$ is concave and $C^1$ on $[0,\infty)$ (both pieces equal $263/144$ with slope $5/6$ at $b=7/12$) but strictly concave only on $(7/12,\infty)$. The payoff of the example is $f(t,1,(-a,a))=\delta(t)g_1(a)$, $f(t,2,(b,-b))=\delta(t)g_2(b)$ with $\delta(t)=\tfrac12e^{-t}+\tfrac12e^{-2t}$, its time derivative $f_t$ uses $\delta'$, and the candidate equilibrium is
--   $$
--   Q^*\sim(a^*,b^*)=\Big(\frac5{12},\frac7{12}\Big).
--   $$
--
--   The example is the paper's demonstration that a weak equilibrium need not be strong.
--
--   **Formalization Note** State 1 is `0 : Fin 2`, state 2 is `1 : Fin 2`. $g_2$ is defined on all of $\mathbb R$ with the case split $b<7/12$ exactly as printed; only $b\ge0$ is ever used, since admissible rows have nonnegative rates.
-- source:
--   Huang & Zhou, Strong and Weak Equilibria for Time-Inconsistent Stochastic Control in Continuous Time, arXiv:1809.09243v3, p. 13, Example 4.3

import Mathlib
import Definitions.Def_StrongWeakEq_TwoState_TwoStateModel

namespace StrongWeakEq.TwoState

/-- Example 4.3, p. 13: `g₁(a) = −a²`. -/
def ex43g₁ (a : ℝ) : ℝ := -a ^ 2

/-- Example 4.3, p. 13: `g₂(b) = 193/144 + (5/6) b` for `b < 7/12`, `2 − (1 − b)²` for `b ≥ 7/12`. -/
noncomputable def ex43g₂ (b : ℝ) : ℝ :=
  if b < 7 / 12 then 193 / 144 + 5 / 6 * b else 2 - (1 - b) ^ 2

/-- Example 4.3, p. 13: the StrongWeakEq.Existence.payoff with `λ = 1/2`, `ρ = 1`, `ρ' = 2` and `g₁`, `g₂` above. -/
noncomputable def ex43 : ℝ → Fin 2 → (Fin 2 → ℝ) → ℝ :=
  twoStatePayoff (1 / 2) 1 2 ex43g₁ ex43g₂

/-- The time derivative of `ex43` (with `δ'` in place of `δ`), the `f_t` of Lemma 3.2. -/
noncomputable def ex43Deriv : ℝ → Fin 2 → (Fin 2 → ℝ) → ℝ :=
  twoStatePayoffDeriv (1 / 2) 1 2 ex43g₁ ex43g₂

/-- Example 4.3, p. 13: the candidate `Q* ∼ (a*, b*) = (5/12, 7/12)`. -/
noncomputable def Qstar : Matrix (Fin 2) (Fin 2) ℝ :=
  gen (5 / 12) (7 / 12)

end StrongWeakEq.TwoState


