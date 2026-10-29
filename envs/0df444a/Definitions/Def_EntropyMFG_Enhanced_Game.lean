-- Prove2me | Definitions.Def_EntropyMFG_Enhanced_Game
-- name    : EntropyMFG_Enhanced_Game
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:23:43.391265+00:00
-- url     : https://prove2.me/theorems/ea32013d-da8e-4d13-a4eb-f2b39c0618e6
-- title:
--   The original enhanced-entropy game and all five admissibility clauses
-- statement:
--   Fix a finite positive horizon $T$ and $A,B,D,Q,\bar Q,\lambda_{SE}>0$, $\lambda_{CE}\ge0$. Population state laws have Lebesgue densities and defined finite means $m_s=\int x\,\mu_s(dx)$, with $\mu_t=\nu$; each population action law $\alpha_s(\cdot;x)$ is a density. No constant mean or equilibrium is assumed.
--
--   For a randomized policy process $\pi$, the original dynamics have drift $\int[A(m_s-X_s)+Bu]\pi_s(u)du$ and diffusion $D\sqrt{\int u^2\pi_s(u)du}$. Action second moments are required to exist almost everywhere in time and probability, as needed to define this SDE. A Markov feedback is a density-valued map whose probabilities of Borel action sets are measurable in time and state.
--
--   The running reward is $-Q(X_s-m_s)^2/2+\lambda_{SE}H_{SE}(\pi_s)+\lambda_{CE}H_{CE}(\pi_s,\alpha_s,\mu_s)$ and the terminal reward is $-\bar Q(X_T-m_T)^2/2$. The cross-entropy term is absent when its coefficient is zero. Opposite infinite entropy contributions cannot be combined. The realized time integral and its total expected payoff must be defined and finite; integrability is imposed on the total reward, not separately on its components.
--
--   Admissibility contains exactly the source's five requirements: a density almost surely at each time, progressive probabilities of every Borel action set, a unique strong solution of the original SDE, finite expected total payoff, and a measurable Markov feedback realizing the policy measures simultaneously in time almost surely. All density-valued policies satisfying these clauses are eligible, without a Gaussian or bounded-control restriction. The game value is the extended-real supremum of their real payoffs, with the state and payoff represented by witnesses. Empty and unbounded sets retain their extended-real suprema.
-- source:
--   Guo, Xu, Zariphopoulou, Entropy Regularization for Mean Field Games with Learning, arXiv:2010.00145v2, https://arxiv.org/abs/2010.00145v2, §2 pp. 4–5, (2.2)–(2.6), admissibility (i)–(v); §3.2 pp. 9–10, (MFG-EE)

import Definitions.Def_EntropyMFG_Enhanced_Stochastic

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
noncomputable section

namespace EntropyMFG.Enhanced

structure Parameters where
  T : ℝ
  A : ℝ
  B : ℝ
  D : ℝ
  Q : ℝ
  Qbar : ℝ
  lambdaSE : ℝ
  lambdaCE : ℝ
  T_pos : 0 < T
  A_pos : 0 < A
  B_pos : 0 < B
  D_pos : 0 < D
  Q_pos : 0 < Q
  Qbar_pos : 0 < Qbar
  lambdaSE_pos : 0 < lambdaSE
  lambdaCE_nonneg : 0 ≤ lambdaCE

/-- Population densities and their finite first moments; no candidate mean is imposed. -/
def Population (t T : ℝ) (ν : Measure ℝ) (μ : ℝ → Measure ℝ)
    (α : ℝ → ℝ → ℝ → ℝ) : Prop :=
  μ t = ν ∧
  (∀ s ∈ Icc t T, (∃ ρ : ℝ → ℝ, IsDensity ρ ∧ μ s = densityMeasure ρ) ∧
    Integrable (fun x : ℝ => x) (μ s)) ∧
  (∀ s ∈ Icc t T, ∀ x, IsDensity (α s x))

def populationMean (μ : ℝ → Measure ℝ) (s : ℝ) : ℝ := ∫ x, x ∂(μ s)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Policy process: time, sample, action. No Gaussian restriction. -/
abbrev Policy (Ω : Type*) := ℝ → Ω → ℝ → ℝ

/-- Measurable density-valued Markov feedback, tested on every Borel action set. -/
def Feedback (t T : ℝ) (f : ℝ → ℝ → ℝ → ℝ) : Prop :=
  (∀ s ∈ Icc t T, ∀ x, IsDensity (f s x)) ∧
  ∀ Z : Set ℝ, MeasurableSet Z →
    Measurable (fun p : Icc t T × ℝ => densityMeasure (f p.1 p.2) Z)

def originalDrift (p : Parameters) (μ : ℝ → Measure ℝ) (π : Policy Ω)
    (s : ℝ) (ω : Ω) (x : ℝ) : ℝ :=
  ∫ u, (p.A * (populationMean μ s - x) + p.B * u) * π s ω u

def originalDiffusion (p : Parameters) (π : Policy Ω)
    (s : ℝ) (ω : Ω) (_x : ℝ) : ℝ :=
  p.D * Real.sqrt (∫ u, u^2 * π s ω u)

/-- The actual MFG-EE equation, with its action integrals defined almost everywhere. -/
def OriginalState (p : Parameters) (P : Measure Ω) (F : Filtration ℝ mΩ)
    (W : ℝ → Ω → ℝ) (t : ℝ) (ξ : Ω → ℝ) (μ : ℝ → Measure ℝ)
    (π : Policy Ω) (X : ℝ → Ω → ℝ) : Prop :=
  (∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Icc t p.T)),
    Integrable (fun u => u^2 * π s ω u) volume) ∧
  UniqueStrongSolution P F W t p.T ξ (originalDrift p μ π) (originalDiffusion p π) X

/-- Running reward with both entropy signs as printed. Cross entropy is absent at lambdaCE=0. -/
def RunningReward (p : Parameters) (μ : ℝ → Measure ℝ) (α : ℝ → ℝ → ℝ → ℝ)
    (s x : ℝ) (π : ℝ → ℝ) (r : EReal) : Prop :=
  ∃ hs hc : EReal, HasShannonEntropy π hs ∧
    (if p.lambdaCE = 0 then hc = 0 else HasCrossEntropy π (α s) (μ s) hc) ∧
    DefinedSum ((p.lambdaSE : EReal) * hs) ((p.lambdaCE : EReal) * hc) ∧
    r = ((-p.Q / 2 * (x - populationMean μ s)^2 : ℝ) : EReal) +
      (p.lambdaSE : EReal) * hs + (p.lambdaCE : EReal) * hc

/-- Finite total expected payoff. Integrability is imposed on the total realized reward,
not on each separate entropy term or on a fourth state moment. -/
def HasPayoff (p : Parameters) (P : Measure Ω) (t : ℝ)
    (μ : ℝ → Measure ℝ) (α : ℝ → ℝ → ℝ → ℝ)
    (π : Policy Ω) (X : ℝ → Ω → ℝ) (v : ℝ) : Prop :=
  ∃ r : ℝ → Ω → EReal, ∃ R : Ω → ℝ,
    (∀ᵐ ω ∂P,
      (∀ᵐ s ∂(volume.restrict (Icc t p.T)),
        RunningReward p μ α s (X s ω) (π s ω) (r s ω)) ∧
      HasExtendedIntegral (volume.restrict (Icc t p.T)) (fun s => r s ω) (R ω)) ∧
    Integrable (fun ω => R ω - p.Qbar / 2 * (X p.T ω - populationMean μ p.T)^2) P ∧
    v = ∫ ω, R ω - p.Qbar / 2 * (X p.T ω - populationMean μ p.T)^2 ∂P

/-- All five clauses on p.5. Equality of policy measures holds simultaneously in time. -/
def Admissible (p : Parameters) (P : Measure Ω) (F : Filtration ℝ mΩ)
    (W : ℝ → Ω → ℝ) (t : ℝ) (ξ : Ω → ℝ)
    (μ : ℝ → Measure ℝ) (α : ℝ → ℝ → ℝ → ℝ)
    (π : Policy Ω) (X : ℝ → Ω → ℝ) (v : ℝ) : Prop :=
  (∀ s ∈ Icc t p.T, ∀ᵐ ω ∂P, IsDensity (π s ω)) ∧
  (∀ Z : Set ℝ, MeasurableSet Z →
    ProgressiveOn F t p.T (fun s ω => densityMeasure (π s ω) Z)) ∧
  OriginalState p P F W t ξ μ π X ∧
  HasPayoff p P t μ α π X v ∧
  ∃ f : ℝ → ℝ → ℝ → ℝ, Feedback t p.T f ∧
    ∀ᵐ ω ∂P, ∀ s ∈ Icc t p.T,
      densityMeasure (π s ω) = densityMeasure (f s (X s ω))

/-- Actual supremum over all admissible policy processes, with state and payoff witnesses.
Empty and unbounded sets retain -infinity and +infinity respectively. -/
def gameValue (p : Parameters) (P : Measure Ω) (F : Filtration ℝ mΩ)
    (W : ℝ → Ω → ℝ) (t : ℝ) (ξ : Ω → ℝ)
    (μ : ℝ → Measure ℝ) (α : ℝ → ℝ → ℝ → ℝ) : EReal :=
  sSup {z : EReal | ∃ π X v, Admissible p P F W t ξ μ α π X v ∧ z = (v : EReal)}

end EntropyMFG.Enhanced


