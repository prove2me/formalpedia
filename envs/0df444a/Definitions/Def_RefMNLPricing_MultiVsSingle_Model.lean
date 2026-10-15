-- Prove2me | Definitions.Def_RefMNLPricing_MultiVsSingle_Model
-- name    : RefMNLPricing_MultiVsSingle_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T11:42:23.41998+00:00
-- url     : https://prove2.me/theorems/fbc1770a-555f-4516-ae7e-124b1c770b8d
-- title:
--   §2, §4.3, pp. 7–27 — kinked MNL revenue, reference path, V⋆, optimal and single-price steady states, ζ₁, ζ₂, κ, κ_{i,1}, κ_{i,2}
-- statement:
--   This file defines the objects of §4.3 that compare the multi-product dynamic pricing model with reference effects under multinomial-logit (MNL) demand with a single-price policy: the single-price value (25), single-price steady states, and the constants $\zeta_1,\zeta_2,\kappa_{i,1},\kappa_{i,2}$. The model itself (utility, shares, revenue, reference path, $V^\star$, optimal steady states, the ceiling assumption, $\kappa$) is imported from the shared model modules of this paper and recalled below.
--
--   **Products and parameters.** There are $n$ products $N=\{1,\dots,n\}$. Product $i$ has intrinsic utility $a_i$, price sensitivity $b_i$, gain sensitivity $c_i^+$ and loss sensitivity $c_i^-$. Given a price vector $p$ and a reference-price vector $r$, the deterministic utility of product $i$ is
--   $$
--   u_i(p,r)=a_i-b_ip_i+c_i^+(r_i-p_i)_+-c_i^-(p_i-r_i)_+ ,\qquad (x)_+=\max\{x,0\},
--   $$
--   the market share is $q_i(p,r)=e^{u_i}/(1+\sum_{k\in N}e^{u_k})$ and the single-period revenue is $\Pi(p,r)=\sum_{i\in N}p_i\,q_i(p,r)$ (equations (2)–(4)). Product $i$ is loss-averse, loss-neutral or gain-seeking according as $c_i^+<c_i^-$, $c_i^+=c_i^-$ or $c_i^+>c_i^-$ (Definition 2).
--
--   **Dynamics and values.** Prices and reference prices lie in the box $\mathcal P^n=[0,p_H]^n$. Reference prices evolve by exponential smoothing $r^{t+1}=\alpha r^t+(1-\alpha)p^t$ (1). The discounted revenue of a price sequence is $\sum_{t\ge0}\beta^t\,\Pi(p^t,r^t)$, and the optimal value $V^\star(r^0)$ is its supremum over all price sequences in $\mathcal P^n$. A **myopic selection** maps each $r\in\mathcal P^n$ to a maximiser of $\Pi(\cdot,r)$ over $\mathcal P^n$ (7). The ceiling quantity $\chi=\max_i 1/(b_i+\min\{c_i^+,c_i^-\})$ and the right-hand side of (9) define the standing assumption $p_H\ge\hat p_H$, where $\hat p_H$ solves (9).
--
--   **Steady states.** A vector $x\in\mathcal P^n$ is an **optimal steady state** (Definition 4) when the constant price path $x$, started from reference $x$, is optimal: $V^\star(x)\le \Pi(x,x)/(1-\beta)$. The **single-price value** (25) from a uniform reference $y_0\mathbf 1$ is the supremum of the discounted revenue over uniform price sequences $y^t\mathbf 1$, $y^t\in[0,p_H]$; a scalar $y\in[0,p_H]$ is a **steady state of the single-product-based policy** when the constant uniform path $y\mathbf 1$ from reference $y\mathbf 1$ attains that value.
--
--   **Constants.** $\kappa=(1-\beta)/(1-\alpha\beta)$; for identical parameters $a,b,c$ and the common myopic steady-state price $p^{m\star}$,
--   $$
--   \zeta_1=\exp(a+\log n+c\,p^{m\star}),\qquad \zeta_2=\frac{2\alpha b+c(\alpha+1)}{(\alpha b+c)(b+c)};
--   $$
--   and for loss-neutral products ($c_i=c_i^+=c_i^-$), $\kappa_{i,1}=(b_i+c_i)^2+\beta(\alpha b_i+c_i)^2$ and $\kappa_{i,2}=2(b_i+c_i\kappa)[b_i(1+\alpha^2\beta)+c_i(1+\alpha\beta)]$ (Remark 4).
--
--   These definitions are the common vocabulary of every statement in the mission.
--
--   **Formalization Note.** Products are indexed by `Fin n` (the paper's product $i$ is index $i-1$). The share (3) is defined directly; the Gumbel derivation is motivation. $V^\star$ is a supremum over price sequences rather than over stationary policies (for this deterministic problem the two coincide). Steady states are encoded in sequence form, so "the optimal policy has no steady state" quantifies over every optimal policy. $\max_i$ in $\chi$ is `⨆ i`, which is $0$ when $n=0$. The standing assumptions ($b>0$, $c^\pm\ge0$, $\alpha\in[0,1]$, $\beta\in[0,1)$, $p_H>0$, $p_H\ge\hat p_H$) are hypotheses of the theorems, not part of the definitions. $\zeta_2$ divides by $\alpha b+c$; theorems using it assume $\alpha b+c>0$.
-- source:
--   Guo, Jiang, Shen, Multi-Product Dynamic Pricing with Reference Effects Under Logit Demand, SSRN 4189049 (version of 2024-05-25), pp. 7–11 (Definitions 1–2, (1)–(9), §2.4), p. 19 (Definition 4), p. 22 (κ in Theorem 5), p. 25 ((25), ζ₁, ζ₂ in Theorem 7), p. 27 (κ_{i,1}, κ_{i,2} in Remark 4)

import Mathlib
import Definitions.Def_RefMNLPricing_GainSeeking_Model
import Definitions.Def_RefMNLPricing_Gap_Model
import Definitions.Def_RefMNLPricing_Myopic_Model
import Definitions.Def_RefMNLPricing_SteadyState_Model

namespace RefMNLPricing.MultiVsSingle

/-! Model of Guo, Jiang, Shen, *Multi-Product Dynamic Pricing with Reference Effects Under Logit
Demand* (SSRN 4189049, version of 2024-05-25), §2, pp. 7–11.

Products are indexed by `Fin n` (the paper's product `i` is index `i - 1`). The parameters are
`a b cp cm : Fin n → ℝ` for the intrinsic utilities `a`, the price sensitivities `b`, and the
reference-price sensitivities `c⁺` (`cp`, gains) and `c⁻` (`cm`, losses). The paper's standing
assumptions `b > 0`, `c⁺, c⁻ ≥ 0`, `α ∈ [0, 1]`, `β ∈ [0, 1)`, `p_H > 0` are hypotheses of the
theorems, not part of these definitions. -/

variable {n : ℕ}

/-- The value of the single-price problem (25), p. 25, from the uniform reference price `y₀ · 1`:
the supremum of the discounted revenue over all admissible **uniform** price sequences
`p^t = y^t · 1`, `y^t ∈ P = [0, p_H]`. The reference path (1) started at `y₀ · 1` and driven by
uniform prices stays uniform, `r^t = r^t · 1`, as in (25). -/
noncomputable def singleValue (a b cp cm : Fin n → ℝ) (α β pH : ℝ) (y₀ : ℝ) : ℝ :=
  ⨆ y : ℕ → Set.Icc (0 : ℝ) pH,
    RefMNLPricing.Gap.disc a b cp cm α β (fun t _ => (y t : ℝ)) (fun _ => y₀)

/-- A steady state of the single-product-based policy `p^s` (p. 25, with the steady-state notion
of p. 15), in sequence form: `y ∈ P` and the constant uniform price path `y · 1`, started from the
reference `y · 1`, is optimal for the single-price problem (25) from `y · 1`. -/
def IsSingleSteadyState (a b cp cm : Fin n → ℝ) (α β pH : ℝ) (y : ℝ) : Prop :=
  y ∈ Set.Icc 0 pH ∧
    singleValue a b cp cm α β pH y ≤
      RefMNLPricing.Myopic.revenue a b cp cm (fun _ => y) (fun _ => y) / (1 - β)

/-- `ζ₁ := exp(a + log n + c p^{m⋆})` of Theorem 7, p. 25, for identical parameters `a`, `c` and the
common myopic steady-state price `pms = p^{m⋆}`. -/
noncomputable def zeta1 (n : ℕ) (a c pms : ℝ) : ℝ :=
  Real.exp (a + Real.log n + c * pms)

/-- `ζ₂ := [2αb + c(α + 1)] / [(αb + c)(b + c)]` of Theorem 7, p. 25 (identical parameters `b`,
`c`). The denominator vanishes only when `α b + c = 0`; theorems using `ζ₂` assume `0 < α b + c`. -/
noncomputable def zeta2 (α b c : ℝ) : ℝ :=
  (2 * α * b + c * (α + 1)) / ((α * b + c) * (b + c))

/-- `κ_{i,1} := (b_i + c_i)² + β(α b_i + c_i)²` of Remark 4, p. 27 (loss-neutral, `c_i = c_i⁺ = c_i⁻`). -/
def kappa1 (b c : Fin n → ℝ) (α β : ℝ) (i : Fin n) : ℝ :=
  (b i + c i) ^ 2 + β * (α * b i + c i) ^ 2

/-- `κ_{i,2} := 2 (b_i + c_i κ) · [b_i(1 + α²β) + c_i(1 + αβ)]` of Remark 4, p. 27, with
`κ = (1 − β)/(1 − αβ)`. -/
noncomputable def kappa2 (b c : Fin n → ℝ) (α β : ℝ) (i : Fin n) : ℝ :=
  2 * (b i + c i * RefMNLPricing.SteadyState.kappa α β) * (b i * (1 + α ^ 2 * β) + c i * (1 + α * β))

end RefMNLPricing.MultiVsSingle


