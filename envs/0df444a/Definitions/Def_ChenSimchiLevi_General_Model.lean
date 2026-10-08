-- Prove2me | Definitions.Def_ChenSimchiLevi_General_Model
-- name    : ChenSimchiLevi_General_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T19:45:05.589929+00:00
-- url     : https://prove2.me/theorems/7c403fc2-b041-40e1-a560-59041841ec57
-- title:
--   Finite-horizon inventory and pricing model with general random demand
-- statement:
--   The model has periods $t=1,\ldots,T$, an inventory level $x$ before ordering, and a post-order level $y\ge x$. The firm chooses expected demand $d$ in $[\underline d_t,\overline d_t]$. Its price is the inverse-demand value $P_t(d)$, so expected revenue is $R_t(d)=dP_t(d)$. Actual demand is $\alpha_t d+\beta_t$, where $(\alpha_t,\beta_t)$ has law $\mu_t$. Unsatisfied demand is backlogged. Ordering $y-x>0$ costs $k+c_t(y-x)$, and end-of-period inventory incurs $h_t(y-\alpha_t d-\beta_t)$.
--
--   With terminal value $v_{T+1}=0$, the model defines the one-period profit and Bellman value by
--   $$g_t(y,d)=R_t(d)-c_ty+\mathbb E[-h_t(y-\alpha_t d-\beta_t)+v_{t+1}(y-\alpha_t d-\beta_t)],$$
--   $$v_t(x)=c_tx+\sup_{y\ge x}\{-k\mathbf 1_{\{y>x\}}+\sup_{d\in[\underline d_t,\overline d_t]}g_t(y,d)\}.$$
--
--   The accompanying assumptions encode the paper's demand moments, inverse-demand continuity and decrease, revenue concavity, convex holding cost, coercivity, growth and demand moments. This model is the common data for Theorem 4.1 and its dynamic-programming milestones.
--
--   **Formalization Note** Expectations are real integrals and their integrability is explicit. Periods outside $1,\ldots,T$ have no economic meaning. The model adds $c_{T+1}=0$, $c_t\ge0$, and $k\ge0$; these are needed for the stated finite-horizon result. Temporal independence is used to justify the Bellman recursion, which is taken as the definition here and uses only each period's marginal law.
-- source:
--   Chen, Simchi-Levi, Coordinating Inventory Control and Pricing Strategies with Random Demand and Fixed Ordering Cost: The Finite Horizon Case, Operations Research 52(6) (2004), pp. 888–889, §2, Assumptions 1–5, equations (1)–(3)

import Mathlib

set_option autoImplicit false

noncomputable section

namespace ChenSimchiLevi.General

open MeasureTheory Filter Set
open scoped BigOperators

/-- Finite-horizon inventory and expected-demand data of §2. -/
structure Model where
  T : ℕ
  k : ℝ
  c : ℕ → ℝ
  h : ℕ → ℝ → ℝ
  dlo : ℕ → ℝ
  dhi : ℕ → ℝ
  P : ℕ → ℝ → ℝ
  μ : ℕ → Measure (ℝ × ℝ)
  ρ : ℕ

/-- The fixed ordering cost is paid exactly when the order is positive. -/
def δ (u : ℝ) : ℝ := if 0 < u then 1 else 0

/-- Expected holding or backlog cost after choosing expected demand `d`. -/
def Model.G (M : Model) (t : ℕ) (y d : ℝ) : ℝ :=
  ∫ ε, M.h t (y - ε.1 * d - ε.2) ∂(M.μ t)

/-- Assumptions 1–5, expressed in expected-demand coordinates, plus the
nonnegative costs and terminal unit cost needed for the finite-horizon result. -/
structure Model.Assumptions (M : Model) : Prop where
  horizon : 0 < M.T
  fixed_nonneg : 0 ≤ M.k
  unit_nonneg : ∀ t ∈ Finset.Icc 1 M.T, 0 ≤ M.c t
  terminal_unit : M.c (M.T + 1) = 0
  law_probability : ∀ t ∈ Finset.Icc 1 M.T, IsProbabilityMeasure (M.μ t)
  alpha_integrable : ∀ t ∈ Finset.Icc 1 M.T, Integrable (fun ε : ℝ × ℝ => ε.1) (M.μ t)
  alpha_mean : ∀ t ∈ Finset.Icc 1 M.T, (∫ ε, ε.1 ∂(M.μ t)) = 1
  beta_integrable : ∀ t ∈ Finset.Icc 1 M.T, Integrable (fun ε : ℝ × ℝ => ε.2) (M.μ t)
  beta_mean : ∀ t ∈ Finset.Icc 1 M.T, (∫ ε, ε.2 ∂(M.μ t)) = 0
  demand_interval : ∀ t ∈ Finset.Icc 1 M.T, M.dlo t ≤ M.dhi t
  price_continuous : ∀ t ∈ Finset.Icc 1 M.T,
    ContinuousOn (M.P t) (Set.Icc (M.dlo t) (M.dhi t))
  price_decreasing : ∀ t ∈ Finset.Icc 1 M.T,
    StrictAntiOn (M.P t) (Set.Icc (M.dlo t) (M.dhi t))
  revenue_concave : ∀ t ∈ Finset.Icc 1 M.T,
    ConcaveOn ℝ (Set.Icc (M.dlo t) (M.dhi t)) (fun d => d * M.P t d)
  holding_convex : ∀ t ∈ Finset.Icc 1 M.T, ConvexOn ℝ Set.univ (M.h t)
  holding_coercive : ∀ t ∈ Finset.Icc 1 M.T, ∀ d ∈ Set.Icc (M.dlo t) (M.dhi t),
    Tendsto (fun y => M.G t y d) (cocompact ℝ) atTop
  holding_left : ∀ t ∈ Finset.Icc 1 M.T, ∀ d ∈ Set.Icc (M.dlo t) (M.dhi t),
    Tendsto (fun y => M.c t * y + M.G t y d) atBot atTop
  holding_right : ∀ t ∈ Finset.Icc 1 M.T, ∀ d ∈ Set.Icc (M.dlo t) (M.dhi t),
    Tendsto (fun y => (M.c t - M.c (t + 1)) * y + M.G t y d) atTop atTop
  holding_integrable : ∀ t ∈ Finset.Icc 1 M.T, ∀ y, ∀ d ∈ Set.Icc (M.dlo t) (M.dhi t),
    Integrable (fun ε : ℝ × ℝ => M.h t (y - ε.1 * d - ε.2)) (M.μ t)
  holding_nonneg : ∀ t ∈ Finset.Icc 1 M.T, ∀ y, ∀ d ∈ Set.Icc (M.dlo t) (M.dhi t),
    0 ≤ M.G t y d
  holding_growth : ∀ t ∈ Finset.Icc 1 M.T, ∃ C : ℝ,
    ∀ y, ∀ d ∈ Set.Icc (M.dlo t) (M.dhi t),
      M.G t y d ≤ C * (1 + |y| ^ M.ρ)
  demand_moment : ∀ t ∈ Finset.Icc 1 M.T, ∀ d ∈ Set.Icc (M.dlo t) (M.dhi t),
    Integrable (fun ε : ℝ × ℝ => |ε.1 * d + ε.2| ^ M.ρ) (M.μ t)

/-- One-period profit when the continuation value is `V`. -/
def Model.gWith (M : Model) (V : ℝ → ℝ) (t : ℕ) (y d : ℝ) : ℝ :=
  d * M.P t d - M.c t * y +
    ∫ ε, (-M.h t (y - ε.1 * d - ε.2) + V (y - ε.1 * d - ε.2)) ∂(M.μ t)

/-- Best one-period profit over the admissible expected-demand interval. -/
def Model.GstarWith (M : Model) (V : ℝ → ℝ) (t : ℕ) (y : ℝ) : ℝ :=
  sSup ((M.gWith V t y) '' Set.Icc (M.dlo t) (M.dhi t))

/-- Ordering objective after subtracting the linear inventory term. -/
def Model.orderObjWith (M : Model) (V : ℝ → ℝ) (t : ℕ) (x y : ℝ) : ℝ :=
  -M.k * δ (y - x) + M.GstarWith V t y

/-- Backward recursion by the number of periods remaining. -/
def Model.vAux (M : Model) : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun x =>
      M.c (M.T - n) * x +
        sSup ((M.orderObjWith (M.vAux n) (M.T - n) x) '' Set.Ici x)

/-- The profit-to-go; in particular, `v (T+1) = 0`. -/
def Model.v (M : Model) (t : ℕ) : ℝ → ℝ := M.vAux (M.T + 1 - t)

/-- The paper's `g_t` with continuation `v_{t+1}`. -/
def Model.g (M : Model) (t : ℕ) : ℝ → ℝ → ℝ := M.gWith (M.v (t + 1)) t

/-- The optimized expected-demand value `g_t(y,d_t(y))`. -/
def Model.Gstar (M : Model) (t : ℕ) : ℝ → ℝ := M.GstarWith (M.v (t + 1)) t

/-- Ordering objective in period `t`. -/
def Model.orderObj (M : Model) (t : ℕ) : ℝ → ℝ → ℝ :=
  M.orderObjWith (M.v (t + 1)) t

/-- An `(s,S,A,p)` policy's post-order inventory level. -/
def sSAOrder (s S : ℝ) (A : Set ℝ) (x : ℝ) : ℝ := by
  classical
  exact if x < s ∨ x ∈ A then S else x

end ChenSimchiLevi.General

end


