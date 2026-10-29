-- Prove2me | Definitions.Def_PeskirShiryaev_General_MarkovModel
-- name    : PeskirShiryaev_General_MarkovModel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:23:47.24759+00:00
-- url     : https://prove2.me/theorems/09c20256-2dd7-456b-8fc0-d01ea2f3fab3
-- title:
--   Section 2.2 — strong Markov process and regularity assumptions
-- statement:
--   Let $d\ge1$ and $E=\mathbb R^d$ with its Borel sigma algebra. A process $X=(X_t)_{t\ge0}$ is defined on a measurable sample space with a right-continuous filtration and a measurable family of probability laws $(P_x)_{x\in E}$. It is adapted, starts at $x$ almost surely under $P_x$, and has right-continuous sample paths. It is left-continuous along increasing stopping times at their finite limit, almost surely under each $P_x$.
--
--   The strong Markov property is expressed by the conditional transition identity: for every stopping time $\tau$ finite $P_x$-almost surely, every $s\ge0$, and every bounded Borel function $f:E\to\mathbb R$,
--   $$E_x[f(X_{\tau+s})\mid\mathcal F_\tau]=E_{X_\tau}[f(X_s)]\quad P_x\text{-a.s.}$$
--
--   These are the process assumptions used in the continuous-time Markovian stopping theory. No payoff, value, or optimal stopping rule is part of this model.
--
--   **Formalization Note** States are functions from $\{0,\ldots,d-1\}$ to $\mathbb R$, time is nonnegative real, and Markov times may equal infinity. The process is retained on its original measurable probability-space realization, before the book's optional canonical-space identification. The bounded Borel transition identity is the usual strong Markov property. Evaluation through conversion of an infinite time to zero occurs only outside the almost-sure finite event on which the identity is used.
-- source:
--   Peskir and Shiryaev, Optimal Stopping and Free-Boundary Problems, Birkhäuser Verlag, 2006, DOI 10.1007/978-3-7643-7390-0, pp. 34–35 (PDF 54–55), Section 2.2, paragraph 1.

import Mathlib

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace PeskirShiryaev.General

abbrev State (d : ℕ) := Fin d → ℝ

/-- Right continuity at every time on the same sample path. -/
def RightContinuousPaths {Ω A : Type*} [TopologicalSpace A]
    (Y : ℝ≥0 → Ω → A) (ω : Ω) : Prop :=
  ∀ t, ContinuousWithinAt (fun s => Y s ω) (Ici t) t

/-- Section 2.2, pp. 34–35. The process may be given on any realization of its
path law; the strong Markov identity is expressed with bounded Borel state tests. -/
structure MarkovModel (d : ℕ) (Ω : Type*) [mΩ : MeasurableSpace Ω] where
  dimension_pos : 0 < d
  P : State d → Measure Ω
  probability : ∀ x, IsProbabilityMeasure (P x)
  measurable_laws : ∀ A : Set Ω, MeasurableSet A → Measurable (fun x => P x A)
  filtration : Filtration ℝ≥0 mΩ
  filtration_rightContinuous : filtration.IsRightContinuous
  X : ℝ≥0 → Ω → State d
  adapted : Adapted filtration X
  starts : ∀ x, ∀ᵐ ω ∂P x, X 0 ω = x
  rightContinuous : ∀ ω, RightContinuousPaths X ω
  strongMarkov : ∀ (x : State d) (τ : Ω → ℝ≥0∞)
    (hτ : IsStoppingTime filtration τ),
    (∀ᵐ ω ∂P x, τ ω < ⊤) →
    ∀ (s : ℝ≥0) (f : State d → ℝ), Measurable f →
      Bornology.IsBounded (Set.range f) →
      (P x)[fun ω => f (X ((τ ω).toNNReal + s) ω) | hτ.measurableSpace]
        =ᵐ[P x] (fun ω => ∫ ω', f (X s ω') ∂P (X (τ ω).toNNReal ω))
  leftContinuous_stopping : ∀ (x : State d) (τ : Ω → ℝ≥0∞)
    (τn : ℕ → Ω → ℝ≥0∞),
    IsStoppingTime filtration τ →
    (∀ n, IsStoppingTime filtration (τn n)) →
    (∀ ω, Monotone (fun n => τn n ω)) →
    (∀ᵐ ω ∂P x, Tendsto (fun n => τn n ω) atTop (𝓝 (τ ω))) →
    ∀ᵐ ω ∂P x, τ ω < ⊤ →
      Tendsto (fun n => X (τn n ω).toNNReal ω) atTop (𝓝 (X (τ ω).toNNReal ω))

end PeskirShiryaev.General


