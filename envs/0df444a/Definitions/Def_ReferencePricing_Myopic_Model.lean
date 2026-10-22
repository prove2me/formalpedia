-- Prove2me | Definitions.Def_ReferencePricing_Myopic_Model
-- name    : ReferencePricing_Myopic_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T09:07:41.610986+00:00
-- url     : https://prove2.me/theorems/fd77626e-0130-4a50-a370-11dddef36ce8
-- title:
--   Reference-price demand model: demand, profit, base and reference profit, slope λ(r), and the memory recursion (1)
-- statement:
--   Fix a **base demand** $d : \mathbb{R} \to \mathbb{R}$ (the paper's $D(p,p)$) and a **reference effect** $R : \mathbb{R} \times \mathbb{R} \to \mathbb{R}$, where $R(x, r)$ is the change in demand caused by a perceived gain $x = r - p$ at reference price $r$. The model's objects are:
--
--   - demand $D(p, r) = d(p) + R(r - p, r)$ (this is the paper's definition $R(r-p, r) = D(p,r) - D(p,p)$, read backwards);
--   - short-term profit $\Pi(p, r) = p\,D(p, r)$ (unit cost $c = 0$);
--   - base profit $\pi(p) = p\,d(p) = \Pi(p,p)$;
--   - reference profit $\Pi^R(p, r) = p\,R(r-p, r)$, so that $\Pi = \pi + \Pi^R$;
--   - the slope of the reference effect at zero gain, $\lambda(r) = R_x(0, r)$;
--   - the reference path of a price sequence $(p_t)_{t \ge 0}$ from $r_0$, given by memory equation (1):
--   $$r_{t+1} = \alpha\, r_t + (1-\alpha)\, p_t, \qquad t \ge 0.$$
--
--   These are the primitives of the whole paper; every later object (value function, optimal and myopic policies) is built from them.
--
--   **Formalization Note.** The data are the pair $(d, R)$ rather than $D$, so the model identity $R(0, r) = 0$ (Remark 1) is a hypothesis of the theorems that use it. $\lambda(r)$ is Lean's `deriv` of $x \mapsto R(x, r)$ at $0$, which is $0$ where $R$ is not differentiable; the theorems assume differentiability (Assumption 2), so this default is never used.
-- source:
--   Popescu and Wu, Dynamic Pricing Strategies with Reference Effects, Operations Research 55(3), 2007, p. 415, Section 2 (definition of R) and p. 417, Section 3, Eq. (1), and Section 4 (π, Π^R, λ)

import Mathlib

namespace ReferencePricing.Myopic

/-- Demand `D(p, r) = D(p, p) + R(r - p, r)` (Popescu–Wu 2007, p. 415): base demand `d p = D(p, p)`
plus the reference effect `R x r` evaluated at the perceived gain `x = r - p`. -/
def demand (d : ℝ → ℝ) (R : ℝ → ℝ → ℝ) (p r : ℝ) : ℝ :=
  d p + R (r - p) r

/-- Short-term profit `Π(p, r) = p D(p, r)` with unit cost `c = 0` (p. 417). -/
def profit (d : ℝ → ℝ) (R : ℝ → ℝ → ℝ) (p r : ℝ) : ℝ :=
  p * demand d R p r

/-- Base profit `π(p) = Π(p, p) = p D(p, p)` (p. 417). -/
def baseProfit (d : ℝ → ℝ) (p : ℝ) : ℝ :=
  p * d p

/-- Reference profit `Π^R(p, r) = p R(r - p, r)` (p. 417). -/
def refProfit (R : ℝ → ℝ → ℝ) (p r : ℝ) : ℝ :=
  p * R (r - p) r

/-- Slope of the reference effect at zero gain, `λ(r) = R_x(0, r)` (p. 417). -/
noncomputable def refSlope (R : ℝ → ℝ → ℝ) (r : ℝ) : ℝ :=
  deriv (fun x => R x r) 0

/-- Reference price formation (1), p. 417: `r_0` given and `r_{t+1} = α r_t + (1 - α) p_t`
for the price sequence `p`. -/
def refPath (α r₀ : ℝ) (p : ℕ → ℝ) : ℕ → ℝ
  | 0 => r₀
  | t + 1 => α * refPath α r₀ p t + (1 - α) * p t

end ReferencePricing.Myopic


