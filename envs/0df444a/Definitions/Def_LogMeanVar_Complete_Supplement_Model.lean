-- Prove2me | Definitions.Def_LogMeanVar_Complete_Supplement_Model
-- name    : LogMeanVar_Complete_Supplement_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T22:58:01.838151+00:00
-- url     : https://prove2.me/theorems/30feece2-91fa-4a16-ada9-7ce9f9d7ad33
-- title:
--   §2.1, pp. 7–8 — general scalar market and actual state/log-return SDEs
-- statement:
--   A scalar market has horizon $T>0$, deterministic time–state coefficients $r,\mu,\sigma,m,\nu$, and a feedback stock fraction $\pi(t,y,x)$. The stock and state Brownian motions share a filtration and have cross bracket $\rho t$, with $-1\le\rho\le1$. The state and log wealth satisfy
--
--   $$dX_t=m(t,X_t)dt+\nu(t,X_t)dB^X_t,\qquad dR_t=[r(t,X_t)+(\mu-r)(t,X_t)\pi_t-\tfrac12\sigma(t,X_t)^2\pi_t^2]dt+\sigma(t,X_t)\pi_t dB_t.$$
--
--   The separate printed-admissibility predicate retains the almost-sure finiteness of the conditional expected squared exposure at the current time, exactly as in $A_t$ on p. 8. The conditioning filtration is an explicit argument. Nonnegative conditional expectations use bounded truncations and an extended nonnegative supremum. These relations provide the common stochastic setting, without inferring a Markov property from the state SDE.
--
--   **Formalization Note** Itô integrals use the published step-approximation relation in the common filtration, shifted after a restart. A cutoff changes only exceptional paths or times outside the investment horizon. Initial wealth may be any measurable random current wealth, including every deterministic starting value. Wealth is the positive process $\exp R$.
-- source:
--   Dai, Jin, Kou, Xu, A Dynamic Mean-Variance Analysis for Log Returns, SSRN 3437268 (version of Aug 2019), pp. 7–8, (1), (5), (6), A_t

import Mathlib
import Definitions.Def_EllsbergLearning_IsBrownianWrt
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false

namespace LogMeanVar.Complete.Supplement

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Dai, Jin, Kou, Xu, A Dynamic Mean-Variance Analysis for Log Returns,
SSRN 3437268 (version of Aug 2019), pp. 7–8, (1), (5), (6).
General scalar coefficients; no constant-coefficient or constant-preference restriction. -/
structure Model where
  T : ℝ
  r : ℝ → ℝ → ℝ
  μ : ℝ → ℝ → ℝ
  σ : ℝ → ℝ → ℝ
  m : ℝ → ℝ → ℝ
  ν : ℝ → ℝ → ℝ

abbrev Policy := ℝ → ℝ → ℝ → ℝ

/-- The source's right continuity in time, positive volatility and positive horizon.
No uniqueness/Markov assumption is inferred from these conditions. -/
def Model.Standing (M : Model) : Prop :=
  0 < M.T ∧ (∀ t ∈ Set.Icc 0 M.T, ∀ x, 0 < M.σ t x) ∧
  ∀ t ∈ Set.Ico 0 M.T, ∀ x, ContinuousWithinAt (fun s => M.r s x) (Set.Icc t M.T) t ∧
    ContinuousWithinAt (fun s => M.μ s x) (Set.Icc t M.T) t ∧
    ContinuousWithinAt (fun s => M.σ s x) (Set.Icc t M.T) t ∧
    ContinuousWithinAt (fun s => M.m s x) (Set.Icc t M.T) t ∧
    ContinuousWithinAt (fun s => M.ν s x) (Set.Icc t M.T) t

/-- The adapted coefficient processes required in §2.1, evaluated on the actual
state. This is separate from temporal right continuity of the deterministic maps. -/
def Model.AdaptedAlong (M : Model) (F : Filtration ℝ≥0 mΩ) (X : ℝ → Ω → ℝ) : Prop :=
  ∀ t ∈ Set.Icc 0 M.T,
    StronglyMeasurable[F t.toNNReal] (fun ω => M.r t (X t ω)) ∧
    StronglyMeasurable[F t.toNNReal] (fun ω => M.μ t (X t ω)) ∧
    StronglyMeasurable[F t.toNNReal] (fun ω => M.σ t (X t ω)) ∧
    StronglyMeasurable[F t.toNNReal] (fun ω => M.m t (X t ω)) ∧
    StronglyMeasurable[F t.toNNReal] (fun ω => M.ν t (X t ω))

/-- Brownian motions in the SAME filtration, with cross bracket ρt, expressed by
its compensated product martingale. The scalar Brownian notion is published prior art.
This retains ρ=0 and ρ=±1. -/
def CorrelatedNoise (P : Measure Ω) (F : Filtration ℝ≥0 mΩ)
    (B W : ℝ≥0 → Ω → ℝ) (ρ : ℝ) : Prop :=
  ρ ∈ Set.Icc (-1 : ℝ) 1 ∧ EllsbergLearning.IsBrownianWrt F P B ∧
    EllsbergLearning.IsBrownianWrt F P W ∧
    Martingale (fun t ω => B t ω * W t ω - ρ * (t : ℝ)) F P

noncomputable def shifted (B : ℝ≥0 → Ω → ℝ) (t : ℝ) : ℝ≥0 → Ω → ℝ :=
  fun u ω => B (t.toNNReal + u) ω - B t.toNNReal ω

/-- A cutoff to a pathwise square-integrable integrand, to satisfy the published
local Itô relation on all paths. It agrees a.s. with H on the finite horizon. -/
noncomputable def cutoff (T : ℝ) (H : ℝ → Ω → ℝ) : ℝ≥0 → Ω → ℝ := by
  classical
  exact fun u ω => if (u : ℝ) ≤ T ∧ IntervalIntegrable (fun s => H s ω ^ 2) volume 0 T
    then H u ω else 0

/-- (5), p.8, actual state SDE. The relation asserts no Markov property. -/
def IsState (M : Model) (P : Measure Ω) (F : Filtration ℝ≥0 mΩ)
    (W : ℝ≥0 → Ω → ℝ) (X : ℝ → Ω → ℝ) : Prop :=
  (∀ t ∈ Set.Icc 0 M.T, StronglyMeasurable[F t.toNNReal] (X t)) ∧
  (∀ᵐ ω ∂P, ContinuousOn (fun t => X t ω) (Set.Icc 0 M.T) ∧
    IntervalIntegrable (fun s => M.m s (X s ω)) volume 0 M.T ∧
    IntervalIntegrable (fun s => M.ν s (X s ω) ^ 2) volume 0 M.T) ∧
  ∃ I : ℝ≥0 → Ω → ℝ,
    EthierKurtz.HasBrownianItoIntegral P (fun u => F u) W
      (cutoff M.T (fun s ω => M.ν s (X s ω))) I ∧
    ∀ t ∈ Set.Icc 0 M.T, ∀ᵐ ω ∂P,
      X t ω = X 0 ω + (∫ s in (0 : ℝ)..t, M.m s (X s ω)) + I t.toNNReal ω

noncomputable def drift (M : Model) (π : Policy) (X R : ℝ → Ω → ℝ)
    (s : ℝ) (ω : Ω) : ℝ :=
  M.r s (X s ω) + (M.μ s (X s ω) - M.r s (X s ω)) * π s (R s ω) (X s ω)
    - M.σ s (X s ω) ^ 2 * π s (R s ω) (X s ω) ^ 2 / 2

/-- (6), p.8, with a possibly random current log wealth ξ. This permits conditional
restarts along an existing path as well as every deterministic starting wealth.
The actual Brownian motion is shifted, with the common shifted filtration.
Neither moments nor the desired equilibrium are part of this solution relation. -/
def IsReturn (M : Model) (P : Measure Ω) (F : Filtration ℝ≥0 mΩ)
    (B : ℝ≥0 → Ω → ℝ) (X : ℝ → Ω → ℝ) (π : Policy)
    (t : ℝ) (ξ : Ω → ℝ) (R : ℝ → Ω → ℝ) : Prop :=
  (∀ s ∈ Set.Icc t M.T, StronglyMeasurable[F s.toNNReal] (R s)) ∧
  (∀ᵐ ω ∂P, ContinuousOn (fun s => R s ω) (Set.Icc t M.T) ∧
    IntervalIntegrable (fun s => drift M π X R s ω) volume t M.T ∧
    IntervalIntegrable (fun s => (M.σ s (X s ω) * π s (R s ω) (X s ω)) ^ 2)
      volume t M.T) ∧
  ∃ I : ℝ≥0 → Ω → ℝ,
    EthierKurtz.HasBrownianItoIntegral P (fun u => F (t.toNNReal + u)) (shifted B t)
      (cutoff (M.T - t) (fun u ω => M.σ (t+u) (X (t+u) ω) *
        π (t+u) (R (t+u) ω) (X (t+u) ω))) I ∧
    ∀ s ∈ Set.Icc t M.T, ∀ᵐ ω ∂P,
      R s ω = ξ ω + (∫ u in t..s, drift M π X R u ω) + I (s-t).toNNReal ω

/-- Nonnegative conditional expectation by increasing bounded truncations.
Unlike real condExp, it retains +∞ and also handles conditionally finite variables
whose unconditional expectation is infinite. All truncations are integrable on a
probability space. The defining supremum is in the COMPLETE lattice ℝ≥0∞. -/
noncomputable def lowerCE (P : Measure Ω) (G : MeasurableSpace Ω)
    (U : Ω → ℝ≥0∞) (ω : Ω) : ℝ≥0∞ :=
  ⨆ n : ℕ, ENNReal.ofReal ((P[fun a => (min (U a) (n : ℝ≥0∞)).toReal | G]) ω)

/-- Dai, Jin, Kou, Xu, SSRN 3437268 (version of Aug 2019), p.8, A_t:
the conditional expected squared exposure is finite almost surely.
This retains the printed conditional condition, rather than requiring an
unconditional finite expectation. Measurability of the energy prevents the
conditional expectation of a nonmeasurable input from taking a default value.
Finite return moments are a separate issue. -/
def PrintedAdmissible (M : Model) (P : Measure Ω) (F : Filtration ℝ≥0 mΩ)
    (X R : ℝ → Ω → ℝ) (π : Policy) (t : ℝ) : Prop :=
  let energy : Ω → ℝ≥0∞ := fun a => ∫⁻ s in Set.Icc t M.T,
    ENNReal.ofReal ((M.σ s (X s a) * π s (R s a) (X s a)) ^ 2)
  AEMeasurable energy P ∧
    ∀ᵐ ω ∂P, lowerCE P (F t.toNNReal) energy ω < ⊤

end LogMeanVar.Complete.Supplement


