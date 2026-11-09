-- Prove2me | Definitions.Def_AutomatedMarketStress557_Persistence_Model
-- name    : AutomatedMarketStress557_Persistence_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:07:29.647895+00:00
-- url     : https://prove2.me/theorems/60491dc8-4739-4d0c-9213-42e4c8b210a9
-- title:
--   Independent symmetric news and the recursive feedback model
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space and $\nu$ a Borel probability measure on $\mathbb R$, with cumulative distribution function $G(x)=\nu(({-\infty},x])$. The model requires $G$ to be continuous, strictly increasing on all of $\mathbb R$, and symmetric: $G(-x)=1-G(x)$. The news variables $\xi_1,\xi_2,\ldots$ have law $\nu$ and are jointly independent. The initial sign $D_0$ has the fair law $\tfrac12\delta_{-1}+\tfrac12\delta_1$ and is independent of the entire news sequence.
--
--   For any real feedback $\beta$ and scale $s>0$, define the positive-time returns recursively by
--
--   $$r_t=\beta D_{t-1}+s\xi_t,\qquad D_t=\operatorname{sgn}(r_t),\qquad t\ge1.$$
--
--   The sign at zero is set to $+1$. The initial magnitude is omitted because only its sign enters this recursion; no stationary return law is imposed at time zero. Also defined are the sign-agreement variables $A_t=D_tD_{t-1}$ and the equal mixture measure of $\beta+s\xi_1$ and $-\beta+s\xi_1$. No claim that these are the actual marginal or transition laws is included in the assumptions.
--
--   This is the minimal operational model needed for the sign-process and persistence statements. It allows news without a density or finite moments.
--
--   **Formalization Note** News index `n` denotes the source's $\xi_{n+1}$. Random variables are considered up to null sets through Mathlib's `HasLaw`. Theorems supply the probability-measure and positive-scale hypotheses; the predicate itself contains only Assumption 1.
-- source:
--   Irene Aldridge, STOC 2027 submission #557 (October 2026), equation (3), PDF p. 2; Assumption 1 and Lemma 4.1, PDF p. 3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/557.pdf

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section

namespace AutomatedMarketStress557.Persistence

/-- Assumption 1, PDF p. 3: the fair initial sign law. -/
def fairSignLaw : Measure ℝ :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac (-1) + (1 / 2 : ℝ≥0∞) • Measure.dirac 1

/-- A total sign convention. Its value at zero is +1; the theorems establish
that no modeled return at a positive time is zero, almost surely. -/
def sign (x : ℝ) : ℝ := if x < 0 then -1 else 1

/-- Exactly the news and initial-sign assumptions of Assumption 1 (PDF p. 3).
`ξ n` is the paper's ξ_(n+1). The initial magnitude is omitted because (3)
uses only its sign. Independence from the entire news vector is joint.
Probability-space and positive-scale hypotheses are supplied at use sites.
No transition, stationarity, moment or episode-law conclusion is assumed. -/
def Model {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ν : Measure ℝ)
    (d₀ : Ω → ℝ) (ξ : ℕ → Ω → ℝ) : Prop :=
  Continuous (cdf ν) ∧ StrictMono (cdf ν) ∧
  (∀ x : ℝ, cdf ν (-x) = 1 - cdf ν x) ∧
  (∀ n : ℕ, HasLaw (ξ n) ν P) ∧ iIndepFun ξ P ∧
  HasLaw d₀ fairSignLaw P ∧ IndepFun d₀ (fun ω n => ξ n ω) P

/-- Equation (3), PDF p. 2. Time zero stores the initial sign; all actual
returns are at times t ≥ 1. Every initial return of that sign gives exactly
the same positive-time path. -/
def returns {Ω : Type*} (β s : ℝ) (d₀ : Ω → ℝ) (ξ : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => d₀
  | n + 1 => fun ω => β * sign (returns β s d₀ ξ n ω) + s * ξ n ω

/-- D_t from equation (3), including the initial sign at t = 0 almost surely. -/
def signs {Ω : Type*} (β s : ℝ) (d₀ : Ω → ℝ) (ξ : ℕ → Ω → ℝ)
    (t : ℕ) (ω : Ω) : ℝ := sign (returns β s d₀ ξ t ω)

/-- Lemma 4.1: `flips n` is A_(n+1); +1 means sign agreement. -/
def flips {Ω : Type*} (β s : ℝ) (d₀ : Ω → ℝ) (ξ : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) : ℝ := signs β s d₀ ξ (n + 1) ω * signs β s d₀ ξ n ω

/-- The actual mixture measure in Theorem 4.2(1), not a point mass or just a CDF. -/
def marginalMixture (ν : Measure ℝ) (β s : ℝ) : Measure ℝ :=
  (1 / 2 : ℝ≥0∞) • Measure.map (fun x : ℝ => β + s * x) ν +
  (1 / 2 : ℝ≥0∞) • Measure.map (fun x : ℝ => -β + s * x) ν

end AutomatedMarketStress557.Persistence


