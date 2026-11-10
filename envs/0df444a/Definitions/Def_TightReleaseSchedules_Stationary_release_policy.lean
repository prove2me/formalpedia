-- Prove2me | Definitions.Def_TightReleaseSchedules_Stationary_release_policy
-- name    : TightReleaseSchedules_Stationary_release_policy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T15:44:03.22413+00:00
-- url     : https://prove2.me/theorems/dc64d5ec-7a96-4379-ba36-7ef7070d2fe2
-- title:
--   Unrestricted causal release policies and actual minimax risk
-- statement:
--   Fix a horizon $T$, dimension $d$, release budget $B$, initial vector $\theta_0\in\mathbb R^d$ and radius $\Delta>0$. A seed can have any measurable space and any probability law; it is sampled independently of the Gaussian rows. A policy gives ordered dates $0\le\tau_1\le\cdots\le\tau_B\le T$ and corresponding vectors $w^{(j)}$. Its information at date $n$ consists precisely of the seed and the first $n$ labeled observations. Dates are stopping times and a vector is measurable when released. Unused slots have date $T$; coincident dates and empty phases are allowed. The initial head is $\theta_0$, and round $t$ uses the last head released by date $t-1$. Every release slot is charged, including time-zero releases and returns to previous heads.
--
--   For a deterministic target path $\theta_{1:T}$, and for a stationary target ball, define
--
--   $$
--   R_T(\pi;\theta_{1:T})=\mathbb E\!\left[\frac12\sum_{t=1}^T\|w_t-\theta_t\|_2^2\right],\qquad
--   R_T^*(B;\Delta,0)=\inf_{\pi\in\Pi_B}\ \sup_{\|\theta-\theta_0\|_2\le\Delta}R_T(\pi;\theta).
--   $$
--   The policy class $\Pi_B$ imposes only timing, measurability and the pathwise budget. Memory, computations, predictor magnitudes and the continuous target ball are unrestricted. A policy has deterministic dates when each date is a fixed number, independent of both the seed and the observations. These objects specify the optimization problem independently of any statistical bound.
--
--   **Formalization Note** Risk is a nonnegative extended expectation, permitting infinite risk without excluding competitors. The infimum is a set infimum over all measurable seed spaces, probability laws and admissible policies, outside the supremum over targets. Targets are never policy inputs. The underlying sampling measure is the product of the seed law and the Gaussian row law. Stopped-head measurability is expressed by measurability of the head, set to zero until its date has occurred.
-- source:
--   Jing Wang, When to Update a Pretrained Model: Tight Release Schedules under Distribution Shift, STOC 2027 submission #1096 (October 2026), §§3.1–3.2, printed p.6, PDF p.7

import Definitions.Def_TightReleaseSchedules_Stationary_gaussian_experiment

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
noncomputable section

namespace TightReleaseSchedules.Stationary

/-- No restriction on the measurable space or distribution of the independent seed. -/
structure RandomSeed where
  space : Type
  measurableSpace : MeasurableSpace space
  law : @Measure space measurableSpace
  probability : @IsProbabilityMeasure space measurableSpace law

attribute [instance] RandomSeed.measurableSpace RandomSeed.probability

abbrev Transcript (s : RandomSeed) (T d : ℕ) := s.space × Data T d

/-- Information at date n: seed and precisely the first n labeled rows. -/
@[instance_reducible] def information (s : RandomSeed) (T d n : ℕ) : MeasurableSpace (Transcript s T d) :=
  MeasurableSpace.comap (fun ω : Transcript s T d =>
    (ω.1, fun i : Fin T => if i.val < n then ω.2 i else (0, 0))) inferInstance

/-- B slots allow coincident dates and padding by T. Validity is separate from raw data. -/
structure ReleasePolicy (s : RandomSeed) (T d B : ℕ) where
  date : Fin B → Transcript s T d → ℕ
  head : Fin B → Transcript s T d → Vector d

/-- Only information, ordering and pathwise quota conditions; no statistical guarantee. -/
def IsCausal {s : RandomSeed} {T d B : ℕ} (π : ReleasePolicy s T d B) : Prop :=
  (∀ j ω, π.date j ω ≤ T) ∧
  (∀ ω, Monotone (fun j => π.date j ω)) ∧
  (∀ j n, @MeasurableSet _ (information s T d n) {ω | π.date j ω ≤ n}) ∧
  (∀ j n, @Measurable _ _ (information s T d n) inferInstance
    (fun ω => if π.date j ω ≤ n then π.head j ω else 0))

/-- Dates are fixed numbers, independent of both seed and observations. -/
def HasDeterministicDates {s : RandomSeed} {T d B : ℕ} (π : ReleasePolicy s T d B) : Prop :=
  ∀ j, ∃ n, ∀ ω, π.date j ω = n

/-- Apply every release made before this prediction, in slot order, including date zero.
Every slot is charged even when its head agrees with a previous head. -/
def deployed {s : RandomSeed} {T d B : ℕ} (θ₀ : Vector d)
    (π : ReleasePolicy s T d B) (ω : Transcript s T d) (i : Fin T) : Vector d :=
  (List.finRange B).foldl (fun w j => if π.date j ω ≤ i.val then π.head j ω else w) θ₀

def policyRisk {s : RandomSeed} {T d B : ℕ} (θ₀ : Vector d)
    (π : ReleasePolicy s T d B) (θ : Fin T → Vector d) : ℝ≥0∞ :=
  ∫⁻ ω : s.space × GaussianRows T d,
    ENNReal.ofReal ((1 / 2 : ℝ) * ∑ i : Fin T,
      ‖deployed θ₀ π (ω.1, observations θ ω.2) i - θ i‖ ^ 2)
    ∂(s.law.prod (gaussianRows T d))

def worstRisk {s : RandomSeed} {T d B : ℕ} (θ₀ : Vector d) (Δ : ℝ)
    (π : ReleasePolicy s T d B) : ℝ≥0∞ :=
  ⨆ θ : {θ : Vector d // ‖θ - θ₀‖ ≤ Δ}, policyRisk θ₀ π (fun _ => θ.val)

/-- Infimum over all seed spaces, all seed laws and all admissible policies, outside
the supremum over deterministic targets. Quantifying in a set avoids a universe restriction
from an indexed infimum over the large type of measurable seed spaces. -/
def minimaxRisk (T d B : ℕ) (θ₀ : Vector d) (Δ : ℝ) : ℝ≥0∞ :=
  sInf {v | ∃ (s : RandomSeed) (π : ReleasePolicy s T d B),
    IsCausal π ∧ v = worstRisk θ₀ Δ π}

def unitSeed : RandomSeed where
  space := Unit
  measurableSpace := inferInstance
  law := Measure.dirac ()
  probability := inferInstance

end TightReleaseSchedules.Stationary


