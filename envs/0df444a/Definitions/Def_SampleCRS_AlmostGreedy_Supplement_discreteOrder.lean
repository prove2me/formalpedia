-- Prove2me | Definitions.Def_SampleCRS_AlmostGreedy_Supplement_discreteOrder
-- name    : SampleCRS_AlmostGreedy_Supplement_discreteOrder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:35:28.216479+00:00
-- url     : https://prove2.me/theorems/313cb2c7-eabc-4883-9c5c-3586be79b7c5
-- title:
--   Finite-mean natural-number laws, discrete convexity and extended expectations
-- statement:
--   For $f:\mathbb N\to\mathbb R$, define $\Delta f(j)=f(j+1)-f(j)$ and $\Delta^2f(j)=\Delta f(j+1)-\Delta f(j)$. Discrete convexity means all second differences are nonnegative; discrete concavity means they are nonpositive. A natural-number law is an arbitrary probability measure on $\mathbb N$ with finite first moment. Its stop loss at $j+1$ is $E[(X-j-1)^+]$, with subtraction in the reals.
--
--   For two such laws $P,Q$, define $D_j=E_P[(X-j-1)^+]-E_Q[(Y-j-1)^+]$. The order $P\ge_{cx}Q$ tests every discrete convex real function integrable under both laws. Signed extended expectations use
--   $$E_P^*[f]=\int f^+\,dP-\int f^-\,dP\quad\text{in }\overline{\mathbb R}.$$
--   On convex tests the negative part is finite under finite-mean laws; on concave tests the positive part is finite. Thus B.1 can retain infinite expectations. The summability predicate for B.2 is exactly the convergence of the nonnegative series $\sum_j(E_P[(X-j-1)^+]+E_Q[(Y-j-1)^+])|\Delta^2 f(j)|$. There is no restriction to finite support, equal means or a common underlying probability space.
-- source:
--   Shaddin Dughmi, Vasilis Livanos, Pranav Nuti, STOC 2027 submission #686 (October 2026), Definitions B.2–B.3 and Theorem B.2 setup, pp.37–38

import Mathlib

open MeasureTheory

namespace SampleCRS.AlmostGreedy.Supplement

def delta (f : ℕ → ℝ) (j : ℕ) : ℝ := f (j + 1) - f j

def delta2 (f : ℕ → ℝ) (j : ℕ) : ℝ := delta f (j + 1) - delta f j

def DiscreteConvex (f : ℕ → ℝ) : Prop := ∀ j, 0 ≤ delta2 f j

def DiscreteConcave (f : ℕ → ℝ) : Prop := ∀ j, delta2 f j ≤ 0

/-- Arbitrary N-supported laws, using their pushforward distributions. There is
no common-space, independence, finite-support or higher-moment assumption. -/
structure NatLaw where
  law : Measure ℕ
  probability : IsProbabilityMeasure law
  finiteMean : Integrable (fun j : ℕ => (j : ℝ)) law

attribute [instance] NatLaw.probability

noncomputable def mean (P : NatLaw) : ℝ := ∫ j, (j : ℝ) ∂P.law

/-- Real subtraction after casting counts, followed by the positive part. -/
noncomputable def stopLoss (P : NatLaw) (j : ℕ) : ℝ :=
  ∫ x, max ((x : ℝ) - (j : ℝ) - 1) 0 ∂P.law

noncomputable def stopDifference (P Q : NatLaw) (j : ℕ) : ℝ := stopLoss P j - stopLoss Q j

def ConvexDominates (P Q : NatLaw) : Prop :=
  ∀ f : ℕ → ℝ, DiscreteConvex f → Integrable f P.law → Integrable f Q.law →
    (∫ j, f j ∂Q.law) ≤ ∫ j, f j ∂P.law

/-- Signed extended expectation. Convex tests under finite-mean laws have a
finite negative part, and concave tests have a finite positive part. Thus on
the domains used in B.1 there is no infinity-minus-infinity ambiguity. -/
noncomputable def extendedE (P : Measure ℕ) (f : ℕ → ℝ) : EReal :=
  (∫⁻ j, ENNReal.ofReal (f j) ∂P).toEReal - (∫⁻ j, ENNReal.ofReal (-f j) ∂P).toEReal

def SecondDifferenceSummable (P Q : NatLaw) (f : ℕ → ℝ) : Prop :=
  Summable (fun j => (stopLoss P j + stopLoss Q j) * |delta2 f j|)

end SampleCRS.AlmostGreedy.Supplement


