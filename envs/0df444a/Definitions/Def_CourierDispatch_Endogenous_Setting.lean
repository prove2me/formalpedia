-- Prove2me | Definitions.Def_CourierDispatch_Endogenous_Setting
-- name    : CourierDispatch_Endogenous_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T01:06:10.583532+00:00
-- url     : https://prove2.me/theorems/6a2e38fd-33fd-4f4a-ab49-308ddbe3cf41
-- title:
--   §3 and §5 — delivery waits, crowded-market revenue, and optimal demand
-- statement:
--   A vendor at the center of a disk of radius $r>0$ serves orders using either one-order dedicated trips or two-order batch trips. Let $\lambda$ be the effective order rate. The paper's service rates and variation coefficients are $\mu_D=3/(4r)$, $C_D=9/8$, and $\mu_B=45\pi/[4r(32+15\pi)]$. The batch coefficient $C_B$ is estimated numerically near $0.583$; it is a parameter restricted to $0.58\le C_B\le0.59$. Write $T_D=3/4$ and $T_B=45\pi/[2(32+15\pi)]$.
--
--   The paper defines the expected waits and limiting revenue rate by
--   $$
--   W_D(\lambda,\mu,C)=\frac{\lambda C}{2\mu(\mu-\lambda)},\qquad
--   W_B(r,\lambda,\mu,C)=\frac1{2\lambda}+\frac{\lambda C}{2\mu(2\mu-\lambda)}+\frac r3,
--   \qquad V_\infty(\lambda,w)=\lambda(1-cw).
--   $$
--   For a finite density factor $n$, the revenue is $V_n(\lambda,w)=\lambda[Q(1-\lambda/(n\Lambda r^2))-cw]$, where $Q=F^{-1}$ is the customer-valuation quantile function. The dedicated and batch objectives insert their respective waits into $V_\infty$. Their optimal revenues are the suprema over $[0,\mu_D)$ and $(0,2\mu_B)$.
--
--   The definitions also specify an optimal demand for the revenue-preferred mode and the induced limiting price $1-cw$. At equal optimal revenues, dedicated delivery is selected. The one-sided demand and price predicates describe the discontinuities claimed in Propositions 3 and 4.
--
--   **Formalization Note** The Lean name `lam` denotes $\lambda$. Real division is total in Lean, so all optimization domains exclude the singular service-rate endpoints; the batch domain also excludes zero. The suprema are of the objective images, not the appendix's closed-form answers. The batch wait uses the paper's Kingman-based closed-form approximation; no stochastic queue is modeled.
-- source:
--   Chen, Hu, Courier Dispatch in On-Demand Delivery, SSRN 3675063 (version of 2022-09-21), pp. 7–12, (4)–(6), (9), (10), (12); p. 16, (14)–(15); Online Appendix p. 2, (A.3)

import Mathlib
import Definitions.Def_CourierDispatch_Exogenous_Setting

namespace CourierDispatch.Endogenous
noncomputable section

/-- Crowded-market revenue, equation (15). -/
def Vinf (c lam w : ℝ) : ℝ := lam * (1 - c * w)
/-- Finite-density revenue, equation (14); Q denotes the inverse c.d.f. -/
def Vn (Q : ℝ → ℝ) (Lam r c : ℝ) (n : ℕ) (lam w : ℝ) : ℝ :=
  lam * (Q (1 - lam / ((n : ℝ) * Lam * r ^ 2)) - c * w)

/-- The dedicated and batch objective functions in (A.3). -/
def VinfD (c r lam : ℝ) : ℝ := Vinf c lam (CourierDispatch.Exogenous.WD lam (CourierDispatch.Exogenous.muD r) CourierDispatch.Exogenous.CD)
def VinfB (CB c r lam : ℝ) : ℝ := Vinf c lam (CourierDispatch.Exogenous.WB r lam (CourierDispatch.Exogenous.muB r) CB)

/-- Stable demand ranges; the zero-demand batch wait is singular. -/
def domD (r : ℝ) : Set ℝ := Set.Ico 0 (CourierDispatch.Exogenous.muD r)
def domB (r : ℝ) : Set ℝ := Set.Ioo 0 (2 * CourierDispatch.Exogenous.muB r)

/-- Optimal crowded-market revenues, the suprema in (A.3). -/
def OptD (c r : ℝ) : ℝ := sSup (VinfD c r '' domD r)
def OptB (CB c r : ℝ) : ℝ := sSup (VinfB CB c r '' domB r)
/-- The normalized difference in optimal revenues from (A.7), defined by (A.3). -/
def G (CB α : ℝ) : ℝ := OptB CB α 1 - OptD α 1

/-- An optimal demand for the revenue-preferred mode; dedicated is selected at a tie. -/
def IsOptDemand (CB c r lam : ℝ) : Prop :=
  if OptD c r < OptB CB c r then
    lam ∈ domB r ∧ VinfB CB c r lam = OptB CB c r
  else
    lam ∈ domD r ∧ VinfD c r lam = OptD c r

/-- The price inducing the selected demand in the crowded-market limit of (1). -/
def optPrice (CB c r lam : ℝ) : ℝ :=
  if OptD c r < OptB CB c r then
    1 - c * CourierDispatch.Exogenous.WB r lam (CourierDispatch.Exogenous.muB r) CB
  else
    1 - c * CourierDispatch.Exogenous.WD lam (CourierDispatch.Exogenous.muD r) CourierDispatch.Exogenous.CD

/-- One-sided demand drop and price rise when wait cost crosses its switching value. -/
def CostJump (CB r cinf : ℝ) : Prop :=
  (∃ ls : ℝ → ℝ, ∀ c, 0 < c → IsOptDemand CB c r (ls c)) ∧
  ∀ ls : ℝ → ℝ, (∀ c, 0 < c → IsOptDemand CB c r (ls c)) →
    ∃ L R PL PR : ℝ, R < L ∧ PL < PR ∧
      Filter.Tendsto ls (nhdsWithin cinf (Set.Iio cinf)) (nhds L) ∧
      Filter.Tendsto ls (nhdsWithin cinf (Set.Ioi cinf)) (nhds R) ∧
      Filter.Tendsto (fun c => optPrice CB c r (ls c))
        (nhdsWithin cinf (Set.Iio cinf)) (nhds PL) ∧
      Filter.Tendsto (fun c => optPrice CB c r (ls c))
        (nhdsWithin cinf (Set.Ioi cinf)) (nhds PR)

/-- One-sided demand drop and price rise when radius crosses its switching value. -/
def RadiusJump (CB c rinf : ℝ) : Prop :=
  (∃ ls : ℝ → ℝ, ∀ r, 0 < r → IsOptDemand CB c r (ls r)) ∧
  ∀ ls : ℝ → ℝ, (∀ r, 0 < r → IsOptDemand CB c r (ls r)) →
    ∃ L R PL PR : ℝ, R < L ∧ PL < PR ∧
      Filter.Tendsto ls (nhdsWithin rinf (Set.Iio rinf)) (nhds L) ∧
      Filter.Tendsto ls (nhdsWithin rinf (Set.Ioi rinf)) (nhds R) ∧
      Filter.Tendsto (fun r => optPrice CB c r (ls r))
        (nhdsWithin rinf (Set.Iio rinf)) (nhds PL) ∧
      Filter.Tendsto (fun r => optPrice CB c r (ls r))
        (nhdsWithin rinf (Set.Ioi rinf)) (nhds PR)

end
end CourierDispatch.Endogenous


