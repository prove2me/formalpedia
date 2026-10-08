-- Prove2me | Definitions.Def_MechanismDesign_Screening_NonlinearPricing
-- name    : MechanismDesign_Screening_NonlinearPricing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T22:43:32.464858+00:00
-- url     : https://prove2.me/theorems/8d5e1f62-d4fa-42dd-9c50-a27464a38c5e
-- title:
--   Nonlinear pricing of a divisible good: valuation, cost, quantity mechanisms, expected profit, regularity
-- statement:
--   This file sets up the nonlinear pricing model of §2.3 of Börgers' book.
--
--   A seller produces any quantity $q\ge 0$ of a divisible good at cost $cq$, with $c>0$. A buyer of type $\theta$ who obtains quantity $q$ and pays $t$ has utility $\theta\,\nu(q)-t$. The function $\nu$ satisfies the standing assumptions of the section:
--   $$\nu(0)=0,\qquad \nu \text{ twice differentiable},\qquad \nu'(q)>0,\ \ \nu''(q)<0 \text{ for all } q\ge 0,$$
--   $$\bar\theta\,\nu'(0)>c,\qquad \lim_{q\to\infty}\bar\theta\,\nu'(q)<c .$$
--   The type distribution $F$ with density $f$ on $[\underline\theta,\bar\theta]$ is as in §2.2.
--
--   1. A **direct mechanism** (Definition 2.5) is a pair $q:[\underline\theta,\bar\theta]\to\mathbb R_+$ (quantity) and $t:[\underline\theta,\bar\theta]\to\mathbb R$ (payment).
--   2. It is **incentive-compatible** if $\theta\nu(q(\theta))-t(\theta)\ge\theta\nu(q(\theta'))-t(\theta')$ for all $\theta,\theta'\in[\underline\theta,\bar\theta]$, and **individually rational** if $\theta\nu(q(\theta))-t(\theta)\ge 0$ for all $\theta$.
--   3. The seller's **expected profit** is $\int_{\underline\theta}^{\bar\theta}\big(t(\theta)-cq(\theta)\big)f(\theta)\,d\theta$.
--   4. The **virtual valuation** is $\theta-\dfrac{1-F(\theta)}{f(\theta)}$, and $F$ is **regular** (Assumption 2.1) if the virtual valuation is (weakly) increasing on $[\underline\theta,\bar\theta]$.
--
--   **Formalization Note** $\nu$ is a function on all of $\mathbb R$ and is required to be twice differentiable on all of $\mathbb R$; only its values on $[0,\infty)$ enter any statement, and any function twice differentiable on $[0,\infty)$ (one-sidedly at $0$) extends to a twice differentiable function on $\mathbb R$, so this is no restriction. The limit condition is stated as: $\bar\theta\,\nu'(q)$ converges as $q\to\infty$ to a limit below $c$. "Increasing" is weak monotonicity, the book's convention (note 3 to Chapter 2).
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, pp.18–19, §2.3, Definition 2.5; p.20, eq. (2.22); p.23, Assumption 2.1

import Mathlib
import Definitions.Def_MechanismDesign_Screening_Model

/-!
# Nonlinear pricing of a divisible good (Börgers, Ch. 2, §2.3, pp.18–23)

The seller produces quantity `q ≥ 0` at cost `c q` (`c > 0`); the buyer of type `θ` has utility
`θ ν(q) − t` from quantity `q` and payment `t`. Standing assumptions (pp.18–19): `ν(0) = 0`,
`ν` twice differentiable, `ν′(q) > 0` and `ν″(q) < 0` for all `q ≥ 0`, `θ̄ ν′(0) > c`, and
`lim_{q→∞} θ̄ ν′(q) < c`. The type distribution is as in §2.2.
-/

namespace MechanismDesign.Screening

open MeasureTheory Filter Topology

/-- The buyer's valuation `ν` and the seller's unit cost `c` of §2.3 (pp.18–19), with the
standing assumptions of the section. `ν` is given as a function on all of `ℝ` (only its values on
`[0, ∞)` are used); "twice differentiable" is required on all of `ℝ`, which is no restriction since
a function twice differentiable on `[0, ∞)` extends to one twice differentiable on `ℝ`. -/
structure NonlinearEnv (θhi : ℝ) where
  /-- The buyer's utility-of-quantity function `ν`. -/
  ν : ℝ → ℝ
  /-- The seller's constant marginal cost `c`. -/
  c : ℝ
  /-- `c > 0`. -/
  c_pos : 0 < c
  /-- `ν(0) = 0`. -/
  ν_zero : ν 0 = 0
  /-- `ν` is differentiable. -/
  ν_differentiable : Differentiable ℝ ν
  /-- `ν′` is differentiable (so `ν` is twice differentiable). -/
  ν'_differentiable : Differentiable ℝ (deriv ν)
  /-- `ν′(q) > 0` for all `q ≥ 0` (`ν` strictly increasing). -/
  ν'_pos : ∀ q : ℝ, 0 ≤ q → 0 < deriv ν q
  /-- `ν″(q) < 0` for all `q ≥ 0` (`ν` strictly concave). -/
  ν''_neg : ∀ q : ℝ, 0 ≤ q → deriv (deriv ν) q < 0
  /-- `θ̄ ν′(0) > c`. -/
  top_gt_cost : c < θhi * deriv ν 0
  /-- `lim_{q→∞} θ̄ ν′(q) < c` (the limit exists and is below `c`). -/
  lim_lt_cost : ∃ L : ℝ, Tendsto (fun q => θhi * deriv ν q) atTop (𝓝 L) ∧ L < c

/-- A **direct mechanism** of §2.3 (Definition 2.5, p.19): a quantity `q : [θ̲, θ̄] → ℝ₊` and a
payment `t : [θ̲, θ̄] → ℝ` as functions of the reported type (deterministic). -/
structure QuantityMechanism (θlo θhi : ℝ) where
  /-- Quantity `q(θ) ≥ 0` sold to the buyer who reports `θ`. -/
  q : ℝ → ℝ
  /-- Payment `t(θ)` of the buyer who reports `θ`. -/
  t : ℝ → ℝ
  /-- `q(θ) ≥ 0` for all `θ ∈ [θ̲, θ̄]`. -/
  q_nonneg : ∀ θ ∈ Set.Icc θlo θhi, 0 ≤ q θ

variable {θlo θhi : ℝ}

/-- Utility `θ ν(q(θ)) − t(θ)` of type `θ` reporting truthfully. -/
def QuantityMechanism.u (E : NonlinearEnv θhi) (m : QuantityMechanism θlo θhi) (θ : ℝ) : ℝ :=
  θ * E.ν (m.q θ) - m.t θ

/-- Incentive compatibility in §2.3 (p.19, as in Definition 2.2): for all `θ, θ′ ∈ [θ̲, θ̄]`,
`θ ν(q(θ)) − t(θ) ≥ θ ν(q(θ′)) − t(θ′)`. -/
def QuantityMechanism.IsIC (E : NonlinearEnv θhi) (m : QuantityMechanism θlo θhi) : Prop :=
  ∀ θ ∈ Set.Icc θlo θhi, ∀ θ' ∈ Set.Icc θlo θhi, θ * E.ν (m.q θ') - m.t θ' ≤ m.u E θ

/-- Individual rationality in §2.3 (p.19, as in Definition 2.3): `θ ν(q(θ)) − t(θ) ≥ 0` for all
`θ ∈ [θ̲, θ̄]`. -/
def QuantityMechanism.IsIR (E : NonlinearEnv θhi) (m : QuantityMechanism θlo θhi) : Prop :=
  ∀ θ ∈ Set.Icc θlo θhi, 0 ≤ m.u E θ

/-- The seller's expected profit `∫_{θ̲}^{θ̄} (t(θ) − c q(θ)) f(θ) dθ` (p.20, (2.22)). -/
noncomputable def expectedProfit (D : TypeDistribution θlo θhi) (E : NonlinearEnv θhi)
    (m : QuantityMechanism θlo θhi) : ℝ :=
  ∫ θ in θlo..θhi, (m.t θ - E.c * m.q θ) * D.f θ

/-- The virtual valuation `θ − (1 − F(θ)) / f(θ)` (p.22, (2.24)). -/
noncomputable def virtualValuation (D : TypeDistribution θlo θhi) (θ : ℝ) : ℝ :=
  θ - (1 - D.F θ) / D.f θ

/-- `F` is **regular** (Assumption 2.1, p.23): `θ − (1 − F(θ)) / f(θ)` is (weakly) increasing in
`θ` on `[θ̲, θ̄]`. -/
def IsRegular (D : TypeDistribution θlo θhi) : Prop :=
  MonotoneOn (virtualValuation D) (Set.Icc θlo θhi)

end MechanismDesign.Screening


