-- Prove2me | Definitions.Def_ReedGGN_Regulator_Supplement_Drivers
-- name    : ReedGGN_Regulator_Supplement_Drivers
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T05:05:37.859978+00:00
-- url     : https://prove2.me/theorems/4c34a1ef-07b0-4e5e-9317-b784a2068660
-- title:
--   §5 — Heavy traffic and all four limiting drivers
-- statement:
--   The heavy-traffic hypotheses are $\rho^N\to1$, $\sqrt N(1-\rho^N)\to\beta\in\mathbb R$ and $\tilde A^N\Rightarrow\tilde\xi$ for an almost surely continuous arrival limit. The initial residual law is equilibrium when $F_0(t)=F_e(t)=\int_0^tG(u)du$. The published standard Brownian bridge is reused with no scaling factor. The continuous centered Gaussian service process $\tilde M_2$ has covariance
--
--   $$E[\tilde M_2(t)\tilde M_2(t+\delta)]=\int_0^tG(t+\delta-u)F(t-u)\,du.$$
--
--   The independent primitive realization comprises $\tilde Q_0,\tilde W_0,\tilde\xi,\tilde M_2$. It constructs
--
--   $$\tilde H=\tilde Q_0\bar F_e,\quad\tilde M_Q=\tilde Q_0^+(G-\bar F_e),\quad\tilde M_1=K_G^{\rm cl}\tilde\xi,\quad\tilde Q_I=\tilde H+\tilde W_0(F_e)+\tilde M_1+\tilde M_2.$$
--
--   The regulator input is $\tilde M_Q+\tilde Q_I-\beta F_e$. The count is shared by $\tilde H$ and $\tilde M_Q$, so these two terms are not assumed independent. Integrability accompanies moments to avoid the default value of a nonintegrable Bochner integral. LimitData contains only data; LimitLaws characterizes laws without asserting convergence. The swapped subscripts in (5.9) are resolved by (5.7), (5.20) and (A.58): the first noise is the arrival convolution, the second is service noise.
-- source:
--   Reed, The G/GI/N Queue in the Halfin–Whitt Regime, arXiv:0912.2837v1, (5.1)–(5.3), p.17; (5.15)–(5.17), p.22; Proposition 5.1, pp.20–21

import Mathlib
import Definitions.Def_ReedGGN_Regulator_Supplement_Convolution
import Definitions.Def_TransitoryQueue_IsBrownianBridge

open MeasureTheory ProbabilityTheory Filter Topology

open scoped NNReal ENNReal

namespace ReedGGN.Regulator.Supplement

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {μ μ₀ : Measure ℝ}

/-- Exact §5.1 arrival FCLT and Halfin–Whitt conditions. ξ is any a.s. continuous process:
 it need not be Gaussian, Brownian, finite-variation, or renewal-driven. -/
def HeavyTraffic (q : QueueFamily Ω P μ μ₀) (ρ : ℕ → ℝ) (β : ℝ) (ξ : Ω → RPath) : Prop :=
  Tendsto ρ atTop (𝓝 1) ∧
  Tendsto (fun n => Real.sqrt (n + 1 : ℕ) * (1 - ρ n)) atTop (𝓝 β) ∧
  (∀ᵐ ω ∂P, Continuous (ξ ω)) ∧
  WeakJ1 P P (fun n ω => one (adiff q ρ n ω)) (fun ω => one (ξ ω))

/-- Equality of the initial residual distribution and the equilibrium distribution. -/
def EquilibriumResidual (μ μ₀ : Measure ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → ProbabilityTheory.cdf μ₀ t = Fe μ t

/-- Centered continuous Gaussian service noise with exactly Proposition 5.1's covariance.
 Gaussianity includes all finite-dimensional laws; covariance is specified for all t,δ≥0.
 Choosing the continuous version is legitimate for this kernel for every service CDF. -/
def ServiceGaussian {S : Type} [MeasurableSpace S] (R : Measure S) (μ : Measure ℝ)
    (M : S → RPath) : Prop :=
  Measurable M ∧ IsGaussianProcess (fun t ω => M ω t) R ∧
  (∀ᵐ ω ∂ R, Continuous (M ω)) ∧
  (∀ t, Integrable (fun ω => M ω t) R ∧ (∫ ω, M ω t ∂ R) = 0) ∧
  ∀ t δ : ℝ≥0, Integrable (fun ω => M ω t * M ω (t + δ)) R ∧
    (∫ ω, M ω t * M ω (t + δ) ∂ R) =
      ∫ u in Set.Icc (0 : ℝ) t, tail μ ((t : ℝ) + δ - u) * ProbabilityTheory.cdf μ ((t : ℝ) - u)

/-- Data for the four primitive limit components; no law or convergence is assumed in this data. -/
structure LimitData (S : Type) where
  q0 : S → ℝ
  bridge : ℝ → S → ℝ
  arrival : S → RPath
  service : S → RPath

noncomputable def bridgeFe {S : Type} (μ : Measure ℝ) (L : LimitData S) (ω : S) : RPath :=
  fun t => L.bridge (Fe μ t) ω

/-- Full independent primitive law, asserted in the conclusion of Proposition 5.2.
 The count and arrival law are copied from their given marginal limits, without fixing
 an arbitrary coupling of those marginals. The bridge is the published standard bridge. -/
def LimitLaws {S : Type} [MeasurableSpace S] (R : Measure S) (μ : Measure ℝ)
    (L : LimitData S) (P : Measure Ω) (q0 : Ω → ℝ) (ξ : Ω → RPath) : Prop :=
  IdentDistrib L.q0 q0 R P ∧ IdentDistrib L.arrival ξ R P ∧
  TransitoryQueue.IsBrownianBridge L.bridge R ∧
  Measurable (fun ω (t : Set.Icc (0 : ℝ) 1) => L.bridge t ω) ∧
  ServiceGaussian R μ L.service ∧
  iIndepFun (fun i : Fin 4 => fun ω =>
    if i = 0 then (fun _ : ℝ≥0 => L.q0 ω)
    else if i = 1 then (fun t => L.bridge (min (t : ℝ) 1) ω)
    else if i = 2 then L.arrival ω
    else L.service ω) R

/-- The primitive tuple on the right of Proposition 5.2. -/
noncomputable def primitiveLimit {S : Type} (μ : Measure ℝ) (L : LimitData S) (ω : S) : State 3 :=
  three (L.q0 ω) (bridgeFe μ L ω) (L.arrival ω) (L.service ω)

/-- All components of (5.15)–(5.17), with the mean drift's minus sign and the initial
 positive-part correction. q0 is shared by H and M_Q; no independence between them is imposed.
 The third coordinate is the arrival path and is transformed with its possible mass at zero. -/
noncomputable def diffusionDriver (μ : Measure ℝ) (β : ℝ) (x : State 3) : RPath :=
  fun t => max x.1 0 * (tail μ t - (1 - Fe μ t)) +
    (x.1 * (1 - Fe μ t) + x.2 0 t + arrivalTransform μ (x.2 1) t + x.2 2 t) - β * Fe μ t

/-- Prelimit initial correction H and M_Q, kept distinct and computed from the same q0diff. -/
noncomputable def hdiff (q : QueueFamily Ω P μ μ₀) (n : ℕ) (ω : Ω) : RPath :=
  fun t => q0diff q n ω * (1 - Fe μ t)
noncomputable def mqdiff (q : QueueFamily Ω P μ μ₀) (n : ℕ) (ω : Ω) : RPath :=
  fun t => max (q0diff q n ω) 0 * (tail μ t - (1 - Fe μ t))
noncomputable def m1diff (q : QueueFamily Ω P μ μ₀) (ρ : ℕ → ℝ) (n : ℕ) (ω : Ω) : RPath :=
  arrivalTransform μ (adiff q ρ n ω)

end ReedGGN.Regulator.Supplement


