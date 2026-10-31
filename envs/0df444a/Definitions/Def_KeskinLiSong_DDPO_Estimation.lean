-- Prove2me | Definitions.Def_KeskinLiSong_DDPO_Estimation
-- name    : KeskinLiSong_DDPO_Estimation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:46:10.098141+00:00
-- url     : https://prove2.me/theorems/104fb257-ed5e-4499-88e7-6216b312b85d
-- title:
--   DDPO estimation, proxy optimization and execution
-- statement:
--   Learner selections are measurable functions of past observed demands, perishability and actions. Execution requires the unconstrained MQLE equations and projection onto Theta, residual construction, beta likelihood maximization and both digamma score equations using all experimental observations, and projection onto Xi. The parametric branch uses unconstrained exponential-family MLE followed by projection onto Phi. The nonparametric objective uses 1/(2 M_t) residual averages and the exact sparse grid with 1/rho in its upper index. Both experimental price assignments are required even at overlaps. Earning decisions maximize the actual proxy, then set y=max(y_unconstrained,x). Undefined quantities and infeasibility cause execution failure; the goal asserts execution rather than taking it as a hypothesis.
-- source:
--   Keskin, Li and Song (2022), Data-Driven Dynamic Pricing and Ordering with Perishable Inventory in a Changing Environment, Management Science, doi:10.1287/mnsc.2021.4011, supplied source.pdf (internally dated January 3, 2021; SSRN 3401188 footers), pp. 11–12, equations (10)–(17)

import Definitions.Def_KeskinLiSong_DDPO_Schedule

open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section

namespace KeskinLiSong.DDPO

inductive NoiseMode where
  | nonparametric
  | exponential (d : ℕ) (family : ExponentialFamily d)

def NoiseMode.version : NoiseMode → Version
  | .nonparametric => .N
  | .exponential _ _ => .E

def NoiseMode.dimension : NoiseMode → ℕ
  | .nonparametric => 0
  | .exponential d _ => d

def NoiseMode.Fits (mode : NoiseMode) (μ : Measure ℝ) : Prop :=
  match mode with
  | .nonparametric => True
  | .exponential _ F => ∃ phi ∈ F.parameterSet, μ = F.law phi

/-- These selections are functions only of observations and previous actions.
The root and argmax relations below, rather than any claimed rate, constrain them. -/
structure Learner (mode : NoiseMode) where
  policy : Policy
  thetaRaw : (k : ℕ) → (Fin k → Observation × Action) → Vector 2
  thetaHat : (k : ℕ) → (Fin k → Observation × Action) → Vector 2
  xiRaw : (k : ℕ) → (Fin k → Observation × Action) → Vector 2
  xiHat : (k : ℕ) → (Fin k → Observation × Action) → Vector 2
  phiHat : (k : ℕ) → (Fin k → Observation × Action) → Vector mode.dimension
  optimum : (k : ℕ) → (Fin k → Observation × Action) → Action
  measurable_thetaRaw : ∀ k, Measurable (thetaRaw k)
  measurable_thetaHat : ∀ k, Measurable (thetaHat k)
  measurable_xiRaw : ∀ k, Measurable (xiRaw k)
  measurable_xiHat : ∀ k, Measurable (xiHat k)
  measurable_phiHat : ∀ k, Measurable (phiHat k)
  measurable_optimum : ∀ k, Measurable (optimum k)

def evaluate {B : Type*} (A : Model) {T : ℕ} (E : Environment A T)
    (π : Policy) (f : (k : ℕ) → (Fin k → Observation × Action) → B)
    (z : Paths T) (t : ℕ) : B :=
  let past := history A E π z (t - 1)
  f past.length past.get

def demandPath (A : Model) {T : ℕ} (E : Environment A T) (π : Policy)
    (z : Paths T) (t : ℕ) : ℝ := (observed A E π z t).1.1

def residual (A : Model) {T : ℕ} (E : Environment A T) (π : Policy)
    (z : Paths T) (theta : Vector 2) (s : ℕ) : ℝ :=
  demandPath A E π z s - meanDemand A theta (actionAt A E π z s).1

def empiricalCost (A : Model) (xi theta : Vector 2) (S : Finset ℕ)
    (M : ℕ) (e : ℕ → ℝ) (p y : ℝ) : ℝ :=
  (∑ s ∈ S, ∫ q,
    (A.h - A.c) * max ((1 - q) * y - meanDemand A theta p - e s) 0 +
    (A.b + p) * max (meanDemand A theta p + e s - (1 - q) * y) 0 ∂perishLaw xi) /
      (2 * (M : ℝ)) + (A.w * (∫ q, q ∂perishLaw xi) + A.c) * y

def empiricalProfit (A : Model) (xi theta : Vector 2) (S : Finset ℕ)
    (M : ℕ) (e : ℕ → ℝ) (p y : ℝ) : ℝ :=
  p * meanDemand A theta p - empiricalCost A xi theta S M e p y

def priceGrid (A : Model) (u : Tuning A) (M : ℕ) : Set ℝ :=
  {p | ∃ i : ℕ, i ≤ Nat.floor ((A.pmax - A.pmin) *
    Real.sqrt ((M : ℝ) / Real.log M) / u.rho) ∧
    p = A.pmin + i * u.rho * Real.sqrt (Real.log M / M)}

def digamma (x : ℝ) : ℝ := deriv (fun z => Real.log (Real.Gamma z)) x

/-- Equations (12)–(13) and unconstrained beta maximum likelihood, followed by
projection. The raw parameters are positive; endpoint observations are not
converted to finite log-likelihoods using log(0)=0. -/
def BetaEstimate (A : Model) (S : Finset ℕ) (q : ℕ → ℝ)
    (raw estimate : Vector 2) : Prop :=
  (∀ s ∈ S, q s ∈ Set.Ioo 0 1) ∧
  0 < raw 0 ∧ 0 < raw 1 ∧
  (∑ s ∈ S, Real.log (q s)) =
    (S.card : ℝ) * (digamma (raw 0) - digamma (raw 0 + raw 1)) ∧
  (∑ s ∈ S, Real.log (1 - q s)) =
    (S.card : ℝ) * (digamma (raw 1) - digamma (raw 0 + raw 1)) ∧
  Maximizes {v : Vector 2 | 0 < v 0 ∧ 0 < v 1}
    (fun v => ∑ s ∈ S, Real.log (betaPDFReal (v 0) (v 1) (q s))) raw ∧
  Projects A.Xi raw estimate

def NoiseMode.Estimate (mode : NoiseMode) (e : List ℝ)
    (phi : Vector mode.dimension) : Prop :=
  match mode with
  | .nonparametric => True
  | .exponential _ F => F.ProjectedMLE e phi

def NoiseMode.IntegrableNoise (mode : NoiseMode) (phi : Vector mode.dimension) : Prop :=
  match mode with
  | .nonparametric => True
  | .exponential _ F => Integrable (fun e : ℝ => e) (F.law phi)

def NoiseMode.proxy (mode : NoiseMode) (A : Model) (xi theta : Vector 2)
    (S : Finset ℕ) (M : ℕ) (e : ℕ → ℝ) (phi : Vector mode.dimension)
    (p y : ℝ) : ℝ :=
  match mode with
  | .nonparametric => empiricalProfit A xi theta S M e p y
  | .exponential _ F => Q A (F.law phi) theta xi p y

def proxyDomain (mode : NoiseMode) (A : Model) (u : Tuning A) (M : ℕ) : Set Action :=
  (if mode.version = .N then priceGrid A u M else A.P) ×ˢ A.Y

/-- The literal DDPO equations for one realized path. Both experimental
assignments are required, including when the printed sets overlap. -/
def ExecutesOn (mode : NoiseMode) (A : Model) (u : Tuning A) {T : ℕ}
    (E : Environment A T) (L : Learner mode) (z : Paths T) : Prop :=
  ∀ t ∈ Finset.Icc 1 T,
    let v := mode.version
    let D := demandPath A E L.policy z
    let S := samples u v T D t
    let M := sampleSize u v T D t
    let raw := evaluate A E L.policy L.thetaRaw z t
    let theta := evaluate A E L.policy L.thetaHat z t
    let xiRaw := evaluate A E L.policy L.xiRaw z t
    let xi := evaluate A E L.policy L.xiHat z t
    let phi := evaluate A E L.policy L.phiHat z t
    let best := evaluate A E L.policy L.optimum z t
    let e := residual A E L.policy z theta
    (t ∈ experimentalAt u v T 0 → actionAt A E L.policy z t = (u.omega1, u.upsilon)) ∧
    (t ∈ experimentalAt u v T 1 → actionAt A E L.policy z t = (u.omega2, u.upsilon)) ∧
    (t ∉ experimental u v T →
      0 < M ∧
      (∑ s ∈ S, (D s - meanDemand A raw (actionAt A E L.policy z s).1)) = 0 ∧
      (∑ s ∈ S, (D s - meanDemand A raw (actionAt A E L.policy z s).1) *
        (actionAt A E L.policy z s).1) = 0 ∧
      Projects A.Theta raw theta ∧
      BetaEstimate A ((Finset.Icc 1 t) ∩ experimental u v T)
        (fun s => (observed A E L.policy z s).1.2) xiRaw xi ∧
      mode.Estimate ((S.sort (· ≤ ·)).map e) phi ∧
      mode.IntegrableNoise phi ∧
      (mode.version = .N → 0 < Real.log M) ∧
      Maximizes (proxyDomain mode A u M) (fun a => mode.proxy A xi theta S M e phi a.1 a.2) best ∧
      actionAt A E L.policy z t = (best.1, max best.2 (stockAt A E L.policy z t)))

/-- Executability is asserted in the goal, rather than required as a premise. -/
def Executes (mode : NoiseMode) (A : Model) (u : Tuning A) {T : ℕ}
    (E : Environment A T) (L : Learner mode) : Prop :=
  Admissible A E L.policy ∧ (∀ᵐ z ∂primitiveLaw A E, ExecutesOn mode A u E L z)

end KeskinLiSong.DDPO


