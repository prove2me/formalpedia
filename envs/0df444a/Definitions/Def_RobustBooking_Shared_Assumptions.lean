-- Prove2me | Definitions.Def_RobustBooking_Shared_Assumptions
-- name    : RobustBooking_Shared_Assumptions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T08:15:50.235798+00:00
-- url     : https://prove2.me/theorems/d1c5d442-2011-4461-aaae-17057aed1441
-- title:
--   Reference-dependent demand $D(p,r)=d(p)+R(r-p,r)$, base and reference profit, slope $\lambda(r)$, and Assumptions 1–3
-- statement:
--   Demand depends on the price $p$ and the reference price $r$. It is described by a **base demand** $d(p)=D(p,p)$ and a **reference effect** $R(x,r)$ of the perceived gain $x=r-p$:
--   $$
--   D(p,r)=d(p)+R(r-p,r).
--   $$
--   This is the paper's definition $R(r-p,r)=D(p,r)-D(p,p)$ read backwards. The per-period profit (variable cost $c=0$) is $\Pi(p,r)=p\,D(p,r)$. The **base profit** is $\pi(p)=p\,d(p)=\Pi(p,p)$, the **reference profit** is $\Pi^R(p,r)=p\,R(r-p,r)$, and the **slope of the reference effect** at zero is $\lambda(r)=R_x(0,r)$.
--
--   With $P=[0,\bar p]$:
--
--   1. **Assumption 1** (Reference-Dependent Demand). $D$ is nonnegative, bounded and continuous on $P\times P$, decreasing in $p$ and increasing in $r$, and $R(\cdot,r)$ is increasing in $x$. The structure also records $R(0,r)=0$, which the definition of $R$ forces (Remark 1).
--   2. **Assumption 2** (Smooth Reference Effect). $R(x,r)$ is twice differentiable in $(x,r)$.
--   3. **Assumption 3** (Profit).
--      (a) $\pi$ is nonmonotonic and concave on $P$.
--      (b) $\Pi_p(r,r)=\pi'(r)-r\lambda(r)$ is strictly decreasing in $r$ on $P$.
--      (c) $\Pi^R(\cdot,r)$ is concave on $P$ for every $r\in P$, and $\Pi^R$ is supermodular on $P\times P$: for $p_1\le p_2$ and $r_1\le r_2$ in $P$,
--   $$
--   \Pi^R(p_2,r_1)+\Pi^R(p_1,r_2)\le\Pi^R(p_2,r_2)+\Pi^R(p_1,r_1).
--   $$
--
--   These are the standing hypotheses of the loss-neutral analysis (Assumption 1 throughout the paper, Assumptions 2–3 throughout §§4.1–4.3).
--
--   **Formalization Note** "Increasing" and "decreasing" are non-strict (`MonotoneOn`/`AntitoneOn`), as Remark 1 only derives $\ge 0$ and $\le 0$. Every property is required on $P$ or $P\times P$, and monotonicity in $x$ on the gains $[r-\bar p,r]$ reachable from $P$. "Nonmonotonic" is encoded as neither `MonotoneOn` nor `AntitoneOn` on $P$. "Twice differentiable" is encoded as: $R$ (uncurried on $\mathbb R^2$) is differentiable and so is its Fréchet derivative. Continuity of the second derivative is not required. Supermodularity is the increasing-differences inequality the paper uses (p. 416).
--
--   **Shared definition.** Serves Popescu–Wu 2007 chunks `01-loss-aversion` (previously `ReferencePricing.LossAversion.Assumptions`) and `03-price-monotonicity` (previously `ReferencePricing.PriceMonotone.Assumptions`); both cite p. 415 (Assumption 1, Remark 1) and p. 417 (Assumptions 2–3, the decomposition $\Pi=\pi+\Pi^R$). Where a theorem needs $\pi'$ to be the true derivative, it adds differentiability of $d$ as its own hypothesis (chunk 03).
-- source:
--   Popescu and Wu, Dynamic Pricing Strategies with Reference Effects, Operations Research 55(3), 2007, p. 415, Assumption 1 and Remark 1; p. 417, Assumptions 2 and 3 and the decomposition Π = π + Π^R

import Mathlib

namespace RobustBooking.Shared

/-- Demand `D(p, r) = d(p) + R(r − p, r)`, p. 415: `d` is the base demand `D(p, p)` and `R` the
reference effect, `R(r − p, r) = D(p, r) − D(p, p)` read backwards (so `R(0, r) = 0`). -/
def demand (d : ℝ → ℝ) (R : ℝ → ℝ → ℝ) (p r : ℝ) : ℝ :=
  d p + R (r - p) r

/-- Short-term profit `Π(p, r) = p D(p, r)` (p. 417, variable cost `c = 0`). -/
def profit (d : ℝ → ℝ) (R : ℝ → ℝ → ℝ) (p r : ℝ) : ℝ :=
  p * demand d R p r

/-- Base profit `π(p) = Π(p, p) = p D(p, p)`, p. 417. -/
def baseProfit (d : ℝ → ℝ) (p : ℝ) : ℝ :=
  p * d p

/-- Reference profit `Π^R(p, r) = p R(r − p, r)`, p. 417. -/
def refProfit (R : ℝ → ℝ → ℝ) (p r : ℝ) : ℝ :=
  p * R (r - p) r

/-- Slope of the reference effect at `x = 0`: `λ(r) = R_x(0, r)`, p. 417. -/
noncomputable def refSlope (R : ℝ → ℝ → ℝ) (r : ℝ) : ℝ :=
  deriv (fun x => R x r) 0

/-- Assumption 1 (Reference-Dependent Demand), p. 415, on the price set `P = [0, p̄]`:
`D` is nonnegative, bounded and continuous on `P × P`, decreasing in `p` and increasing in `r`
(non-strictly), and `R(·, r)` is increasing on the gains `x = r − p ∈ [r − p̄, r]` reachable
from `P`. The field `R_zero` is `R(0, r) = 0` (Remark 1), which the definition of the reference
effect forces. -/
structure Assumption1 (pbar : ℝ) (d : ℝ → ℝ) (R : ℝ → ℝ → ℝ) : Prop where
  R_zero : ∀ r : ℝ, R 0 r = 0
  nonneg : ∀ p ∈ Set.Icc (0 : ℝ) pbar, ∀ r ∈ Set.Icc (0 : ℝ) pbar, 0 ≤ demand d R p r
  bounded : ∃ M : ℝ, ∀ p ∈ Set.Icc (0 : ℝ) pbar, ∀ r ∈ Set.Icc (0 : ℝ) pbar,
    demand d R p r ≤ M
  continuous : ContinuousOn (Function.uncurry (demand d R))
    (Set.Icc (0 : ℝ) pbar ×ˢ Set.Icc (0 : ℝ) pbar)
  antitone_price : ∀ r ∈ Set.Icc (0 : ℝ) pbar,
    AntitoneOn (fun p => demand d R p r) (Set.Icc (0 : ℝ) pbar)
  monotone_ref : ∀ p ∈ Set.Icc (0 : ℝ) pbar,
    MonotoneOn (fun r => demand d R p r) (Set.Icc (0 : ℝ) pbar)
  monotone_gain : ∀ r ∈ Set.Icc (0 : ℝ) pbar,
    MonotoneOn (fun x => R x r) (Set.Icc (r - pbar) r)

/-- Assumption 2 (Smooth Reference Effect), p. 417: `R(x, r)` is twice differentiable in
`(x, r)` — `R` is differentiable on `ℝ²` and so is its Fréchet derivative. -/
structure Assumption2 (R : ℝ → ℝ → ℝ) : Prop where
  differentiable : Differentiable ℝ (Function.uncurry R)
  differentiable_fderiv : Differentiable ℝ (fderiv ℝ (Function.uncurry R))

/-- Assumption 3 (Profit), p. 417, on `P = [0, p̄]`:
(a) `π` is nonmonotonic (neither increasing nor decreasing on `P`) and concave on `P`;
(b) `Π_p(r, r) = π′(r) − r λ(r)` is strictly decreasing on `P`;
(c) `Π^R(·, r)` is concave on `P` for every `r ∈ P`, and `Π^R` is supermodular on `P × P`
(increasing differences, p. 416). -/
structure Assumption3 (pbar : ℝ) (d : ℝ → ℝ) (R : ℝ → ℝ → ℝ) : Prop where
  base_not_monotone : ¬ MonotoneOn (baseProfit d) (Set.Icc (0 : ℝ) pbar)
  base_not_antitone : ¬ AntitoneOn (baseProfit d) (Set.Icc (0 : ℝ) pbar)
  base_concave : ConcaveOn ℝ (Set.Icc (0 : ℝ) pbar) (baseProfit d)
  diag_strictAnti : StrictAntiOn (fun r => deriv (baseProfit d) r - r * refSlope R r)
    (Set.Icc (0 : ℝ) pbar)
  ref_concave : ∀ r ∈ Set.Icc (0 : ℝ) pbar,
    ConcaveOn ℝ (Set.Icc (0 : ℝ) pbar) (fun p => refProfit R p r)
  ref_supermodular : ∀ p₁ ∈ Set.Icc (0 : ℝ) pbar, ∀ p₂ ∈ Set.Icc (0 : ℝ) pbar,
    ∀ r₁ ∈ Set.Icc (0 : ℝ) pbar, ∀ r₂ ∈ Set.Icc (0 : ℝ) pbar, p₁ ≤ p₂ → r₁ ≤ r₂ →
      refProfit R p₂ r₁ + refProfit R p₁ r₂ ≤ refProfit R p₂ r₂ + refProfit R p₁ r₁

end RobustBooking.Shared


