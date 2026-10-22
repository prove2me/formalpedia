-- Prove2me | Definitions.Def_PersonalizedAssortment_IB_PenaltyFunction
-- name    : PersonalizedAssortment_IB_PenaltyFunction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T01:29:19.963476+00:00
-- url     : https://prove2.me/theorems/401cc02f-c7b7-4996-81c1-7b4803e25dbe
-- title:
--   Penalty function $\Psi$ and the competitive-ratio formula $\alpha_{c_{\min}}(\Psi)$
-- statement:
--   A **penalty function** is a map $\Psi:[0,1]\to[0,1]$ that is increasing (non-strictly) and satisfies $\Psi(0)=0$ and $\Psi(1)=1$. The inventory-balancing algorithm discounts the revenue of a product by $\Psi$ evaluated at the fraction of its initial inventory that remains.
--
--   For a real number $C>0$ and a point $x$, write
--   $$R_\Psi(C,x)=\frac{1-x}{\dfrac1C+1-\Psi(x)+\displaystyle\int_{x+1/C}^{1}\Psi(y)\,dy}.$$
--   For a positive integer $m$ (the smallest initial inventory $c_{\min}$), the **competitive-ratio formula** of Theorem 1 is
--   $$\alpha_m(\Psi)=\min_{x\in[0,\,1-1/m]} R_\Psi(m,x).$$
--
--   The formula $\alpha_{c_{\min}}(\Psi)$ is the guarantee of the paper's main theorem. For the linear penalty $\Psi(x)=x$ it equals $1/2$. For the exponential penalty $\Psi(x)=\frac{e}{e-1}(1-e^{-x})$ it tends to $1-1/e$.
--
--   **Formalization Note** $\alpha_m(\Psi)$ is the infimum (`sInf`) of the values $R_\Psi(m,x)$, $x\in[0,1-1/m]$. For a penalty function and $m\ge1$ this set is nonempty (it contains $x=0$). It is bounded below by $0$, since the denominator is at least $1/m>0$. For a continuous $\Psi$ the infimum is attained, so it is the paper's minimum. Values of $\Psi$ outside $[0,1]$ play no role.
-- source:
--   Golrezaei, Nazerzadeh, Rusmevichientong, Real-Time Optimization of Personalized Assortments, Management Sci. 60(6), 2014, https://doi.org/10.1287/mnsc.2014.1939, p. 1537, Section 3 (penalty function); p. 1538, Theorem 1 (formula for alpha_cmin)

import Mathlib

namespace PersonalizedAssortment.IB

/-- A penalty function in the sense of §3, p. 1537: `Ψ : [0, 1] → [0, 1]` is increasing (in the
non-strict sense) with `Ψ(0) = 0` and `Ψ(1) = 1`. Values of `Ψ` outside `[0, 1]` are
irrelevant. -/
def IsPenaltyFunction (Ψ : ℝ → ℝ) : Prop :=
  Set.MapsTo Ψ (Set.Icc 0 1) (Set.Icc 0 1) ∧ MonotoneOn Ψ (Set.Icc 0 1) ∧ Ψ 0 = 0 ∧ Ψ 1 = 1

/-- The ratio inside `α_{c_min}(Ψ)` (Theorem 1, p. 1538), evaluated at a real inventory level
`C` and a point `x`:
`(1 - x) / (1/C + 1 - Ψ(x) + ∫_{x + 1/C}^1 Ψ(y) dy)`. -/
noncomputable def ratioC (Ψ : ℝ → ℝ) (C x : ℝ) : ℝ :=
  (1 - x) / (1 / C + 1 - Ψ x + ∫ y in (x + 1 / C)..1, Ψ y)

/-- `α_{c_min}(Ψ) = min_{x ∈ [0, 1 - 1/c_min]} (1 - x) / (1/c_min + 1 - Ψ(x) + ∫_{x+1/c_min}^1 Ψ(y) dy)`
(Theorem 1, p. 1538), written as the infimum of `ratioC Ψ m` over `[0, 1 - 1/m]`. For a penalty
function and `m ≥ 1` the set is nonempty (it contains the value at `x = 0`) and bounded below by
`0` (the denominator is at least `1/m > 0`), and for a continuous `Ψ` the infimum is attained,
so it is the paper's minimum. -/
noncomputable def alphaC (Ψ : ℝ → ℝ) (m : ℕ) : ℝ :=
  sInf (ratioC Ψ (m : ℝ) '' Set.Icc 0 (1 - 1 / (m : ℝ)))

end PersonalizedAssortment.IB


