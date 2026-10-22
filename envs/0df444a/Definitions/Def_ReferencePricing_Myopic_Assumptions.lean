-- Prove2me | Definitions.Def_ReferencePricing_Myopic_Assumptions
-- name    : ReferencePricing_Myopic_Assumptions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T09:23:15.751184+00:00
-- url     : https://prove2.me/theorems/2386d80e-2407-45c4-ae4f-4d91ceb10a8b
-- title:
--   Assumptions 1–3 of Popescu–Wu: reference-dependent demand, smooth reference effect, concave supermodular profit
-- statement:
--   Let $P = [0, \bar p]$ be the price set and use the model primitives $D$, $\pi$, $\Pi^R$, $\lambda$.
--
--   **Assumption 1 (Reference-Dependent Demand).** On $P \times P$, demand $D(p, r)$ is nonnegative, bounded and (jointly) continuous, decreasing in $p$ for each $r \in P$ and increasing in $r$ for each $p \in P$; and for each $r \in P$ the reference effect $x \mapsto R(x, r)$ is increasing on the gains $x = r - p$, $p \in P$, i.e. on $[r - \bar p, r]$.
--
--   **Assumption 2 (Smooth Reference Effect).** $R(x, r)$ is twice differentiable in $x$ and $r$.
--
--   **Assumption 3 (Profit).** (a) $\pi$ is nonmonotonic and concave on $P$. (b) $\Pi_p(r, r) = \pi'(r) - r\lambda(r)$ is strictly decreasing in $r$ on $P$. (c) For each $r \in P$, $\Pi^R(\cdot, r)$ is concave on $P$, and $\Pi^R$ is supermodular on $P \times P$:
--   $$p_1 \le p_2,\ r_1 \le r_2 \implies \Pi^R(p_2, r_1) + \Pi^R(p_1, r_2) \le \Pi^R(p_2, r_2) + \Pi^R(p_1, r_1).$$
--
--   Assumption 1 is standing throughout the paper; Assumptions 2 and 3 are standing throughout §§4.1–4.3.
--
--   **Formalization Note.** "Increasing/decreasing" is non-strict (Remark 1 of the paper derives only $\ge 0$, $\le 0$ from it). "Nonmonotonic" is encoded as neither `MonotoneOn` nor `AntitoneOn` on $P$. "Twice differentiable" is encoded as differentiability of $R$ and of its Fréchet derivative on $\mathbb{R}^2$ (no continuity of the second derivative). Supermodularity is the paper's increasing-differences definition (p. 416) on $P \times P$.
-- source:
--   Popescu and Wu, Dynamic Pricing Strategies with Reference Effects, Operations Research 55(3), 2007, p. 415, Assumption 1; p. 417, Assumptions 2 and 3

import Mathlib
import Definitions.Def_ReferencePricing_Myopic_Model

namespace ReferencePricing.Myopic

/-- Assumption 1 (Reference-Dependent Demand), p. 415, on the price set `P = [0, p̄]`:
demand `D(p, r)` is nonnegative, bounded and continuous, decreasing in the price `p` and
increasing in the reference price `r`; the reference effect `R(x, r)` is increasing in the gain `x`
(over the gains `x = r - p`, `p ∈ P`, that occur at a reference price `r ∈ P`). -/
structure Assumption1 (d : ℝ → ℝ) (R : ℝ → ℝ → ℝ) (pbar : ℝ) : Prop where
  demand_nonneg : ∀ p ∈ Set.Icc (0 : ℝ) pbar, ∀ r ∈ Set.Icc (0 : ℝ) pbar, 0 ≤ demand d R p r
  demand_bounded : ∃ M : ℝ, ∀ p ∈ Set.Icc (0 : ℝ) pbar, ∀ r ∈ Set.Icc (0 : ℝ) pbar,
    demand d R p r ≤ M
  demand_continuous : ContinuousOn (Function.uncurry (demand d R))
    (Set.Icc (0 : ℝ) pbar ×ˢ Set.Icc (0 : ℝ) pbar)
  demand_antitone_price : ∀ r ∈ Set.Icc (0 : ℝ) pbar,
    AntitoneOn (fun p => demand d R p r) (Set.Icc (0 : ℝ) pbar)
  demand_monotone_ref : ∀ p ∈ Set.Icc (0 : ℝ) pbar,
    MonotoneOn (fun r => demand d R p r) (Set.Icc (0 : ℝ) pbar)
  refEffect_monotone_gain : ∀ r ∈ Set.Icc (0 : ℝ) pbar,
    MonotoneOn (fun x => R x r) (Set.Icc (r - pbar) r)

/-- Assumption 2 (Smooth Reference Effect), p. 417: `R(x, r)` is twice differentiable in `x`
and `r`, encoded as differentiability of `R` and of its Fréchet derivative on `ℝ × ℝ`. -/
def Assumption2 (R : ℝ → ℝ → ℝ) : Prop :=
  Differentiable ℝ (Function.uncurry R) ∧ Differentiable ℝ (fderiv ℝ (Function.uncurry R))

/-- Assumption 3 (Profit), p. 417, on `P = [0, p̄]`:
(a) the base profit `π` is nonmonotonic and concave;
(b) `Π_p(r, r) = π'(r) - r λ(r)` is strictly decreasing in `r`;
(c) the reference profit `Π^R(p, r)` is concave in `p` and supermodular in `(p, r)`
(increasing differences). -/
structure Assumption3 (d : ℝ → ℝ) (R : ℝ → ℝ → ℝ) (pbar : ℝ) : Prop where
  base_not_monotone : ¬ MonotoneOn (baseProfit d) (Set.Icc (0 : ℝ) pbar)
  base_not_antitone : ¬ AntitoneOn (baseProfit d) (Set.Icc (0 : ℝ) pbar)
  base_concave : ConcaveOn ℝ (Set.Icc (0 : ℝ) pbar) (baseProfit d)
  marginal_strictAnti :
    StrictAntiOn (fun r => deriv (baseProfit d) r - r * refSlope R r) (Set.Icc (0 : ℝ) pbar)
  refProfit_concave : ∀ r ∈ Set.Icc (0 : ℝ) pbar,
    ConcaveOn ℝ (Set.Icc (0 : ℝ) pbar) (fun p => refProfit R p r)
  refProfit_supermodular : ∀ p₁ ∈ Set.Icc (0 : ℝ) pbar, ∀ p₂ ∈ Set.Icc (0 : ℝ) pbar,
    ∀ r₁ ∈ Set.Icc (0 : ℝ) pbar, ∀ r₂ ∈ Set.Icc (0 : ℝ) pbar, p₁ ≤ p₂ → r₁ ≤ r₂ →
      refProfit R p₂ r₁ + refProfit R p₁ r₂ ≤ refProfit R p₂ r₂ + refProfit R p₁ r₁

end ReferencePricing.Myopic


