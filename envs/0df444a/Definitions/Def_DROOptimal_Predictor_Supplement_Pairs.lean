-- Prove2me | Definitions.Def_DROOptimal_Predictor_Supplement_Pairs
-- name    : DROOptimal_Predictor_Supplement_Pairs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T08:33:30.700005+00:00
-- url     : https://prove2.me/theorems/bff40623-88dd-4d05-b08c-4520d808b592
-- title:
--   Problem (6), p. 11; §5, p. 24 — continuous-state pairs, prescription disappointment, feasibility and order
-- statement:
--   Let $X\subseteq\mathbb R^n$ and $\Xi\subseteq\mathbb R^d$ be the decision and scenario domains, and let $\mathcal P$ be all Borel probability distributions on $\Xi$, with the weak topology. Write $c(x,\mathbb P)=\int_\Xi\gamma(x,\xi)\,\mathrm d\mathbb P(\xi)$ for the published model cost. An admissible pair $(\hat c,\hat x)$ consists of a jointly continuous predictor $\hat c:X\times\mathcal P\to\mathbb R$ and a quasi-continuous selector $\hat x:\mathcal P\to X$ with
--   $$
--   \hat x(\mathbb P')\in\operatorname*{argmin}_{x\in X}\hat c(x,\mathbb P')\qquad(\mathbb P'\in\mathcal P).
--   $$
--   The selector uses the published general argmin-set definition on the decision subtype. Under a model $\mathbb P$, its disappointment set is $\{\mathbb P':\hat c(\hat x(\mathbb P'),\mathbb P')<c(\hat x(\mathbb P'),\mathbb P)\}$. The pair is feasible in (6) at rate $r$ if it is admissible and the published i.i.d. empirical sampling probability of that set has upper logarithmic rate at most $-r$ for every $\mathbb P\in\mathcal P$.
--
--   The pair order is
--   $$
--   (\hat c_1,\hat x_1)\preceq_{\mathcal X}(\hat c_2,\hat x_2)
--   \iff \hat c_1(\hat x_1(\mathbb P'),\mathbb P')\le\hat c_2(\hat x_2(\mathbb P'),\mathbb P')\quad\forall\mathbb P'\in\mathcal P.
--   $$
--   These definitions extend (6) to the continuous-state regime exactly as specified in §5. They import the existing probability, cost, empirical sampling, predictor-continuity and rate definitions; no finite-support or measurable-selector condition is introduced.
--
--   **Formalization Note** Sampling uses outer probability for arbitrary events, with the published value zero at sample size zero. The log-free rate has the source's $\log0=-\infty$ meaning. At $r=0$ it is automatically satisfied by a probability sequence; membership in the pair family is still required.
-- source:
--   Van Parys, Mohajerin Esfahani & Kuhn, From Data to Decisions: Distributionally Robust Optimization is Optimal, arXiv:1704.04118v3, p. 7, Definition 3; p. 8, Definition 4 (2b); p. 11, (6) and pair order; §5, pp. 23–24

import Mathlib
import Definitions.Def_DROOptimal_Continuous_Setting
import Definitions.Def_GenEmpLik_Consistency_argminSet
import Definitions.Def_DROOptimal_Predictor_Supplement_QuasiContinuity

set_option autoImplicit false

namespace DROOptimal.Predictor.Supplement

variable {n d : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))}
  {Ξ : Set (EuclideanSpace ℝ (Fin d))}

/-- Definition 3, p. 7, reused in §5, pp. 23–24: a minimizer for every realization.
The published general argmin set is applied to the decision subtype, so membership
in X is carried by the type rather than repeated in the minimization. -/
def IsArgminSelector (chat : ↥X → DROOptimal.Continuous.Dist Ξ → ℝ)
    (xhat : DROOptimal.Continuous.Dist Ξ → ↥X) : Prop :=
  ∀ P', xhat P' ∈ GenEmpLik.Consistency.argminSet Set.univ (fun x => chat x P')

/-- The family of pairs in (6), p. 11, interpreted in §5, p. 24.
Predictors are jointly continuous and prescriptors are quasi-continuous argmin
selectors. No measurability or continuity is added for the prescriptor. -/
def IsPair (chat : ↥X → DROOptimal.Continuous.Dist Ξ → ℝ)
    (xhat : DROOptimal.Continuous.Dist Ξ → ↥X) : Prop :=
  DROOptimal.Continuous.IsPredictor chat ∧ QuasiContinuous xhat ∧
    IsArgminSelector chat xhat

/-- Prescription disappointment (2b), Definition 4, p. 8, in the §5 setting. -/
def disappointSet (γ : ↥X → ↥Ξ → ℝ)
    (chat : ↥X → DROOptimal.Continuous.Dist Ξ → ℝ)
    (xhat : DROOptimal.Continuous.Dist Ξ → ↥X)
    (P : DROOptimal.Continuous.Dist Ξ) : Set (DROOptimal.Continuous.Dist Ξ) :=
  {P' | chat (xhat P') P' < DROOptimal.Continuous.cost γ (xhat P') P}

/-- Feasibility in (6), p. 11, reused in §5, p. 24: the pair belongs to the
source family and prescription disappointment has upper logarithmic rate ≤ -r
under every Borel probability model. Uses the published outer sampling probability
and log-free extended nonnegative rate convention, including zero probabilities. -/
def Feasible6 (γ : ↥X → ↥Ξ → ℝ) (r : ℝ)
    (chat : ↥X → DROOptimal.Continuous.Dist Ξ → ℝ)
    (xhat : DROOptimal.Continuous.Dist Ξ → ↥X) : Prop :=
  IsPair chat xhat ∧ ∀ P : DROOptimal.Continuous.Dist Ξ,
    DROOptimal.Continuous.DecaysAtRate (ENNReal.ofReal r)
      (fun T => DROOptimal.Continuous.sampleProb P T (fun P' => P' ∈ disappointSet γ chat xhat P))

/-- The order on pairs, p. 11, reused in §5, p. 24, compares their predicted
optimal values at every realization, rather than comparing at arbitrary decisions. -/
def PairLE (chat₁ : ↥X → DROOptimal.Continuous.Dist Ξ → ℝ)
    (xhat₁ : DROOptimal.Continuous.Dist Ξ → ↥X)
    (chat₂ : ↥X → DROOptimal.Continuous.Dist Ξ → ℝ)
    (xhat₂ : DROOptimal.Continuous.Dist Ξ → ↥X) : Prop :=
  ∀ P', chat₁ (xhat₁ P') P' ≤ chat₂ (xhat₂ P') P'

end DROOptimal.Predictor.Supplement


