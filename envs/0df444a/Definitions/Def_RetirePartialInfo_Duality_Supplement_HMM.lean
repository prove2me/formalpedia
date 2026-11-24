-- Prove2me | Definitions.Def_RetirePartialInfo_Duality_Supplement_HMM
-- name    : RetirePartialInfo_Duality_Supplement_HMM
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T22:19:09.97711+00:00
-- url     : https://prove2.me/theorems/9c4dc497-b433-44a7-b590-b4ff8180b20f
-- title:
--   §3, pp.15–16 — restarted hidden Markov market, actual posterior, innovation and dual stopping payoffs
-- statement:
--   For every current calendar time $t$ and interior prior belief $p$, take a base market law with an independent two-state chain of generator $[[-\lambda_1,\lambda_1],[\lambda_2,-\lambda_2]]$. The drift is $\mu_{\alpha_u}$. The chain is the published general two-state CTMC, with state 0 representing state 1 of this paper. The posterior is a continuous version of $P(\alpha_u=1\mid F^S_u)$; the projected density is a positive continuous version of the base conditional density. Every control and stopping time uses the augmented stock filtration.
--
--   $$y_s=y e^{\beta(s-t)}\frac{B_t\mathcal Z_s}{B_s\mathcal Z_t},\qquad s\ge t.$$
--
--   Each law starts at elapsed time zero. Its posterior and density at elapsed $s-t$ represent the original conditional law at calendar time $s$. The base Itô binder is reused. The innovation and integral equations for the dual-filter diffusion are defined; those equations are not assumed in the optimal-control theorem.
--
--   Restarted $L_1$ is the discounted conjugate expectation. Restarted $L_0$ is the extended-real supremum over every observation stopping time between $t$ and $T_1$, using conditional expectation at the stopping time for its tail reward. These objects provide the general-time extension without identifying a PDE solution with its value by definition.
--
--   **Formalization Note** The law is extended to elapsed $T$ to reuse the immutable density definition; payoffs use only $[0,T-t]$. No absorbing posterior endpoints, nonnegative risk-premium assumption or uniform ellipticity is imposed.
-- source:
--   Chen, Jeon, Wong, Optimal retirement under partial information, SSRN 3683553 (version of June 8, 2021), pp. 15–16, (22)–(28), and pp. 11–12, (13)–(14)

import Mathlib
import Definitions.Def_RetirePartialInfo_Duality_Dual
import Definitions.Def_MFIrrev_Equilibrium_TwoStateChain
import Definitions.Def_RetirePartialInfo_Duality_Supplement_Analysis

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

namespace RetirePartialInfo.Duality.Supplement

/-- Chen, Jeon, Wong, Optimal retirement under partial information, SSRN 3683553
(version of June 8, 2021), pp.15–16, (22)–(28).
Data for the HMM law restarted at calendar time t with initial belief p.
**Formalization Note.** The time index of each base market is elapsed time, starting at zero.
Its law is extended to elapsed T; only [0,T-t] is used by the restarted choice problem.
The independent two-state chain is the published general CTMC, with index 0 = state 1.
The posterior and density are versions of conditional expectations, not free filters. -/
structure HMMFamily (Sample : Type) [MeasurableSpace Sample] where
  market : ℝ → ℝ → Setting Sample
  chain : ℝ → ℝ → ℝ≥0 → Sample → Fin 2
  posterior : ℝ → ℝ → ℝ≥0 → Sample → ℝ
  integralTheta : ℝ → ℝ → ℝ≥0 → Sample → ℝ
  density : ℝ → ℝ → ℝ≥0 → Sample → ℝ

variable {Sample : Type} [MeasurableSpace Sample]

def HMMFamily.Standing (a : Data) (m : HMMFamily Sample) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) a.par.T, ∀ p ∈ Ioo (0 : ℝ) 1,
    let st := m.market t p
    st.Standing a.par ∧
    MFIrrev.Equilibrium.IsTwoStateChain st.P st.𝓕 ![a.rate1, a.rate2] (m.chain t p) ∧
    IndepFun (fun sample s => m.chain t p s sample) (fun sample s => st.W s sample) st.P ∧
    st.P {sample | m.chain t p 0 sample = 0} = ENNReal.ofReal p ∧
    (∀ᵐ sample ∂st.P, ∀ s : ℝ≥0,
      st.μ s sample = if m.chain t p s sample = 0 then a.μ1 else a.μ2) ∧
    IsItoIntegral a.par st (θ a.par st) (m.integralTheta t p) ∧
    IsZVersion a.par st (m.integralTheta t p) (m.density t p) ∧
    (∀ s : ℝ≥0, Measurable[FS a.par st s] (m.posterior t p s)) ∧
    (∀ s : ℝ≥0,
      m.posterior t p s =ᵐ[st.P]
        st.P[(fun sample => if m.chain t p s sample = 0 then (1 : ℝ) else 0) | FS a.par st s]) ∧
    (∀ᵐ sample ∂st.P, ContinuousOn (fun s => m.posterior t p s sample) (Iic a.par.Tn))

/-- Calendar-time dual process in Theorem 3.3, pp.24–25, with the full density ratio.
**Formalization Note.** In the restarted law, elapsed u=s-t and 𝒵_u/𝒵_0 represent
the original 𝒵_s/𝒵_t. B_t/B_s=exp(-r(s-t)); no time-zero simplification is used. -/
noncomputable def dualPath (a : Data) (m : HMMFamily Sample)
    (t p y s : ℝ) (sample : Sample) : ℝ :=
  y * Real.exp (a.par.β * (s-t)) * Bt a.par t *
    m.density t p (s-t).toNNReal sample / (Bt a.par s * m.density t p 0 sample)

noncomputable def beliefPath (m : HMMFamily Sample) (t p s : ℝ) (sample : Sample) : ℝ :=
  m.posterior t p (s-t).toNNReal sample

/-- Innovation (24) from the actual hidden drift and its posterior. -/
noncomputable def innovation (a : Data) (m : HMMFamily Sample) (t p : ℝ)
    (u : ℝ≥0) (sample : Sample) : ℝ :=
  (m.market t p).W u sample + ∫ s in (0 : ℝ)..u,
    θ a.par (m.market t p) s.toNNReal sample - thetaHat a (m.posterior t p s.toNNReal sample)

/-- Integral form of the restarted (27)–(28). `obs` has the observation filtration
and innovation as its driver; the stochastic-integral notion is the immutable base binder.
This predicate is not an assumption of Theorem 3.3: deriving it from the HMM is proof work. -/
def DiffusionEquations (a : Data) (m : HMMFamily Sample) (t p y : ℝ)
    (obs : Setting Sample) (Ip Iy : ℝ≥0 → Sample → ℝ) : Prop :=
  obs.P = (m.market t p).P ∧ obs.𝓕 = FS a.par (m.market t p) ∧
  obs.W = innovation a m t p ∧
  IsItoIntegral a.par obs (fun u sample => beliefVol a (m.posterior t p u sample)) Ip ∧
  IsItoIntegral a.par obs (fun u sample =>
    -thetaHat a (m.posterior t p u sample) * dualPath a m t p y (t+u) sample) Iy ∧
  ∀ᵐ sample ∂obs.P, ∀ u : ℝ≥0, (u : ℝ) ≤ a.par.T-t →
    m.posterior t p u sample = p +
      (∫ s in (0 : ℝ)..u, beliefDrift a (m.posterior t p s.toNNReal sample)) + Ip u sample ∧
    dualPath a m t p y (t+u) sample = y +
      (∫ s in (0 : ℝ)..u, (a.par.β-a.par.r) * dualPath a m t p y (t+s) sample) + Iy u sample

/-- All observation stopping times between the current and mandatory dates, represented
in elapsed time. In the retired branch t≥T1 only immediate retirement is allowed. -/
def Stops (a : Data) (m : HMMFamily Sample) (t p : ℝ) (rho : Sample → ℝ≥0) : Prop :=
  IsStoppingTime (FS a.par (m.market t p)) (fun sample => (rho sample : WithTop ℝ≥0)) ∧
  ∀ sample, (rho sample : ℝ) ≤ max (a.par.T1-t) 0

noncomputable def retiredPayoff (a : Data) (m : HMMFamily Sample) (t p y : ℝ)
    (u : ℝ≥0) (sample : Sample) : ℝ :=
  (∫ s in Icc (t+u) a.par.T, Real.exp (-a.par.β*(s-t)) *
    Utilde (crra a) s (dualPath a m t p y s sample)) +
  Real.exp (-a.par.β*(a.par.T-t)) * Utilde (crra a) a.par.T
    (dualPath a m t p y a.par.T sample)

noncomputable def restartedL1 (a : Data) (m : HMMFamily Sample) (t y p : ℝ) : ℝ :=
  ∫ sample, retiredPayoff a m t p y 0 sample ∂(m.market t p).P

/-- Discounted L at the stopping time uses its stopped σ-algebra, as in (14),
not its tower-collapsed expectation. -/
noncomputable def restartedStopObj (a : Data) (m : HMMFamily Sample) (t p y : ℝ)
    (rho : Sample → ℝ≥0) (hr : Stops a m t p rho) : ℝ :=
  let st := m.market t p
  let tail := st.P[(fun sample => retiredPayoff a m t p y (rho sample) sample) | hr.1.measurableSpace]
  ∫ sample, (∫ s in Icc t (t+rho sample), Real.exp (-a.par.β*(s-t)) *
    (Utilde (crra a) s (dualPath a m t p y s sample) - a.par.ℓ)) + tail sample +
    Real.exp (-a.par.β*(rho sample)) * dualPath a m t p y (t+rho sample) sample *
      b a.par (t+rho sample) ∂st.P

noncomputable def restartedL0 (a : Data) (m : HMMFamily Sample) (t y p : ℝ) : EReal :=
  sSup {v | ∃ rho : Sample → ℝ≥0, ∃ hr : Stops a m t p rho,
    v = (restartedStopObj a m t p y rho hr : EReal)}

end RetirePartialInfo.Duality.Supplement


