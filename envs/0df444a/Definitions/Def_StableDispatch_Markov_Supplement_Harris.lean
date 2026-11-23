-- Prove2me | Definitions.Def_StableDispatch_Markov_Supplement_Harris
-- name    : StableDispatch_Markov_Supplement_Harris
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T09:42:51.431805+00:00
-- url     : https://prove2.me/theorems/adfa3bd4-ee7e-4d4b-923c-a9e98be49036
-- title:
--   §2.4, p. 12 — positive Harris recurrence of a continuous-time process family (occupation-time form with an invariant probability)
-- statement:
--   A **continuous-time process family** on a measurable state space $S$ assigns to every initial state $x$ a probability measure $P_x$ on a sample space and a sample path $t\mapsto X_t$ ($t\ge0$). The **occupation time** of a measurable set $A$ is $\int_0^\infty\mathbf 1_A(X_t)\,dt\in[0,\infty]$.
--
--   Given a set $E\subseteq S$ of states, the family is **Harris recurrent on $E$** if there is a nonzero σ-finite measure $\varphi$ carried by $E$ such that for every measurable $A$ with $\varphi(A)>0$ and every $x\in E$,
--
--   $$P_x\Big(\int_0^\infty\mathbf 1_A(X_t)\,dt=\infty\Big)=1.$$
--
--   A probability measure $\pi$ carried by $E$ is **invariant** if $\pi(A)=\int P_x(X_t\in A)\,\pi(dx)$ for every $t\ge0$ and every measurable $A$. The family is **positive Harris recurrent on $E$** if it is Harris recurrent on $E$ and has an invariant probability measure.
--
--   The paper uses positive Harris recurrence to define the stability region (§2.4) without defining it; this is the standard continuous-time definition of Meyn and Tweedie, stated for an arbitrary measurable state space because the workload space $\mathcal Q^n$ is not locally compact.
--
--   **Formalization Note** Almost-sure statements are `∀ᵐ` under $P_x$; the occupation time is a lower Lebesgue integral in $[0,\infty]$.
-- source:
--   Gamarnik, Tsitsiklis, Zubeldia, Stability, Memory, and Messaging Trade-Offs in Heterogeneous Service Systems, arXiv:2007.07219v1, pp. 11–12, §2.4 (positive Harris recurrence in the definition of the stability region; standard definition, Meyn–Tweedie)

import Mathlib

namespace StableDispatch.Markov.Supplement

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]

/-- A continuous-time process family: for every initial state `x`, a measure `P x` on a sample
space `Ω` and a sample path `X x ω : ℝ → S` (time `t ≥ 0`). The occupation time of a set `A`
along the path started at `x` is `∫_0^∞ 1_A(X_t) dt ∈ [0, ∞]`. -/
def occupation (X : S → Ω → ℝ → S) (x : S) (A : Set S) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ t in Ici (0 : ℝ), A.indicator (fun _ => (1 : ℝ≥0∞)) (X x ω t)

/-- Harris recurrence on the state space `E ⊆ S` (Meyn–Tweedie, continuous time): there is a
nonzero σ-finite measure `φ` carried by `E` such that every measurable `A` with `φ A > 0` has
infinite occupation time almost surely, from every initial state `x ∈ E`. -/
def IsHarrisRecurrent (E : Set S) (P : S → Measure Ω) (X : S → Ω → ℝ → S) : Prop :=
  ∃ φ : Measure S, φ ≠ 0 ∧ SigmaFinite φ ∧ φ Eᶜ = 0 ∧
    ∀ A : Set S, MeasurableSet A → 0 < φ A → ∀ x ∈ E,
      ∀ᵐ ω ∂(P x), occupation X x A ω = ⊤

/-- `π` is an invariant probability measure of the family, carried by `E`:
`π(A) = ∫ P_x(X_t ∈ A) π(dx)` for every `t ≥ 0` and every measurable `A`. -/
def IsInvariantProbability (E : Set S) (P : S → Measure Ω) (X : S → Ω → ℝ → S)
    (π : Measure S) : Prop :=
  IsProbabilityMeasure π ∧ π Eᶜ = 0 ∧
    ∀ t : ℝ, 0 ≤ t → ∀ A : Set S, MeasurableSet A →
      π A = ∫⁻ x, P x {ω | X x ω t ∈ A} ∂π

/-- Positive Harris recurrence on `E`: Harris recurrent, with an invariant probability measure. -/
def IsPositiveHarris (E : Set S) (P : S → Measure Ω) (X : S → Ω → ℝ → S) : Prop :=
  IsHarrisRecurrent E P X ∧ ∃ π : Measure S, IsInvariantProbability E P X π

end

end StableDispatch.Markov.Supplement


