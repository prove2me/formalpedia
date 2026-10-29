-- Prove2me | Definitions.Def_PeskirShiryaev_AmericanPut_Model
-- name    : PeskirShiryaev_AmericanPut_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:25:53.828839+00:00
-- url     : https://prove2.me/theorems/b3d751c2-81f5-4b97-8df8-c10109156c5a
-- title:
--   Geometric Brownian American put model and stopping value
-- statement:
--   Let $B$ be a standard real Brownian motion on a probability space $(\Omega,\mathcal F,P)$, represented with measurable time evaluations and continuous paths. Fix interest rate $r>0$, volatility $\sigma>0$, strike $K>0$, and maturity $T>0$. For initial stock price $x>0$, write
--   $$X_s^x=x\exp\!\left(\sigma B_s+(r-\sigma^2/2)s\right),\qquad G(x)=(K-x)^+.$$
--   A stopping time $\tau$ is admissible at calendar time $t\in[0,T]$ when it is a stopping time for the natural Brownian filtration and $0\le\tau\le T-t$. Define the expected discounted reward and value by
--   $$R(x,\tau)=E[e^{-r\tau}G(X_\tau^x)],\qquad V(t,x)=\sup_{\tau\text{ admissible at }t}R(x,\tau).$$
--   Also set $S_s=X_s^1$ and, for $\delta\ge0$, define $L(\delta)=E[1-\inf_{0\le s\le\delta}S_s]$. These objects describe the stopping problem independently of any boundary equation.
--
--   **Formalization Note** Elapsed times and stopping times are nonnegative reals; calendar times and stock states are real. Expectations are real Bochner integrals. For $x\ge0$ and admissible times, the discounted reward is measurable and bounded by $K$, and the set defining $V$ contains the reward at time zero. A continuous-path version is used on every sample point. The natural filtrations of $B$ and $X^x$ coincide for $x>0$ because their deterministic exponential transformation is invertible. The auxiliary extension at $x=0$ is the identically zero stock, used only to give a nonempty definition of the boundary.
-- source:
--   Peskir and Shiryaev, Optimal Stopping and Free-Boundary Problems, Birkhäuser Verlag, 2006, DOI 10.1007/978-3-7643-7390-0, pp. 379–381 (PDF 395–397), Eqs. (25.2.1)–(25.2.3), (25.2.13)

import Mathlib

open MeasureTheory ProbabilityTheory

open scoped NNReal ENNReal

namespace PeskirShiryaev.AmericanPut

structure Model (Ω : Type*) [MeasurableSpace Ω] where
  P : Measure Ω
  probability : IsProbabilityMeasure P
  B : ℝ≥0 → Ω → ℝ
  measurable : ∀ s, StronglyMeasurable (B s)
  continuous : ∀ ω, Continuous (fun s => B s ω)
  brownian : IsBrownianReal B P
  r : ℝ
  sigma : ℝ
  K : ℝ
  T : ℝ
  r_pos : 0 < r
  sigma_pos : 0 < sigma
  K_pos : 0 < K
  T_pos : 0 < T

noncomputable def Model.filtration {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) :
    Filtration ℝ≥0 ‹MeasurableSpace Ω› :=
  Filtration.natural M.B M.measurable

noncomputable def Model.stock {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω)
    (x : ℝ) (s : ℝ≥0) (ω : Ω) : ℝ :=
  x * Real.exp (M.sigma * M.B s ω + (M.r - M.sigma ^ 2 / 2) * (s : ℝ))

def Model.payoff {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (x : ℝ) : ℝ :=
  max (M.K - x) 0

def Model.Admissible {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω)
    (t : ℝ) (τ : Ω → ℝ≥0) : Prop :=
  IsStoppingTime M.filtration (fun ω => (τ ω : WithTop ℝ≥0)) ∧
    ∀ ω, τ ω ≤ (M.T - t).toNNReal

noncomputable def Model.reward {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω)
    (x : ℝ) (τ : Ω → ℝ≥0) : ℝ :=
  ∫ ω, Real.exp (-M.r * (τ ω : ℝ)) * M.payoff (M.stock x (τ ω) ω) ∂M.P

noncomputable def Model.value {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω)
    (t x : ℝ) : ℝ :=
  sSup {v | ∃ τ : Ω → ℝ≥0, M.Admissible t τ ∧ v = M.reward x τ}

noncomputable def Model.modulus {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω)
    (δ : ℝ≥0) : ℝ :=
  ∫ ω, 1 - sInf ((fun s : ℝ≥0 => M.stock 1 s ω) '' Set.Icc 0 δ) ∂M.P

end PeskirShiryaev.AmericanPut


