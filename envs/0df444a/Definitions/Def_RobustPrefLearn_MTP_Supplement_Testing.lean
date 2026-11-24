-- Prove2me | Definitions.Def_RobustPrefLearn_MTP_Supplement_Testing
-- name    : RobustPrefLearn_MTP_Supplement_Testing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T00:11:52.034195+00:00
-- url     : https://prove2.me/theorems/d623659a-301a-4b0e-9404-bea3459e7f24
-- title:
--   Appendix B.1, pp. 44–45 — general discrete hypothesis testing and policy laws
-- statement:
--   Let $\Theta$, $\mathcal S$ and $\mathcal X$ be arbitrary types of parameters, experiments and outcomes, and let $H_i\subseteq\Theta$ for $i\in[I]$ be the hypotheses. The real mass $f_\theta(x\mid S)$ specifies an outcome law. Assumption 1 requires a true hypothesis at every parameter. Assumption 2 requires positive normalized masses and identifiability:
--   $$\sum_x f_\theta(x\mid S)=1,\quad f_\theta(x\mid S)>0,\quad \theta\ne\theta'\Longrightarrow\exists S,x:\ f_\theta(x\mid S)\ne f_{\theta'}(x\mid S).$$
--   A policy chooses a distribution on experiments from the current history, stops as a function of history, and selects a hypothesis at stopping. Histories have the product law
--   $$\mathbb P_\theta^\pi(H_t=h)=\prod_{\ell=1}^t\lambda_\ell(S_\ell\mid H_{\ell-1}) f_\theta(X_\ell\mid S_\ell),\qquad \mathbb E_\theta^\pi[\tau]=\sum_{t\ge0}\mathbb P_\theta^\pi(\tau>t).$$
--   A policy is $\delta$-accurate if it terminates almost surely and selects a false hypothesis with probability at most $\delta$, at every $\theta$. An accurate family has this property for every $\delta\in(0,1)$. The lower rate is the liminf of the expectation divided by $\log(1/\delta)$ as $\delta\downarrow0$.
--
--   This interface describes general multiple composite hypothesis testing independently of the consumer model. Neither parameters, experiments nor outcomes are assumed finite or countable.
--
--   **Formalization Note** Hypotheses are indexed by `Fin I`, histories are lists newest first, and probability series take values in $[0,\infty]$. Normalization uses the nonnegative series of `ofReal` masses; together with positivity this is exactly probability-mass normalization. Experiment distributions use nonnegative weights whose tsum is one, equivalently a `PMF`. Their supports are countable even when the experiment type is uncountable. Assumptions 1–2 are separate predicates, not conclusions built into the model. The liminf uses the right neighborhood of zero.
-- source:
--   Feng, Caldentey & Ryan, SSRN 3215614, Appendix B.1, pp. 44–45; Assumptions 1–2, p. 44

import Mathlib

open scoped ENNReal Topology

namespace RobustPrefLearn.MTP.Supplement

universe u v w

/-- Appendix B.1, pp.44–45. General discrete experiments, independent of the
consumer model. `H i` is the set of parameters under which hypothesis `i` is true. -/
structure TestingModel (Θ : Type u) (S : Type v) (X : Type w) (I : ℕ) where
  H : Fin I → Set Θ
  mass : Θ → S → X → ℝ

/-- Assumption 1: every parameter has a true hypothesis. -/
def HasTrueHypothesis {Θ : Type u} {S : Type v} {X : Type w} {I : ℕ}
    (M : TestingModel Θ S X I) : Prop := ∀ θ, ∃ i, θ ∈ M.H i

/-- Assumption 2 (B-1)–(B-3). Positivity makes the ENNReal normalization
exactly the printed probability-mass normalization, even for infinite outcomes. -/
def TestingAssumptions {Θ : Type u} {S : Type v} {X : Type w} {I : ℕ}
    (M : TestingModel Θ S X I) : Prop :=
  (∀ θ s, ∑' x, ENNReal.ofReal (M.mass θ s x) = 1) ∧
  (∀ θ s x, 0 < M.mass θ s x) ∧
  ∀ θ θ', θ ≠ θ' → ∃ s x, M.mass θ s x ≠ M.mass θ' s x

/-- The three history-adapted rules of Appendix B.1. Histories are newest first.
Nonnegative display weights are required to sum to one by `TestingAdmissible`. -/
structure TestingPolicy (S : Type v) (X : Type w) (I : ℕ) where
  disp : List (S × X) → S → ℝ≥0∞
  stop : List (S × X) → Prop
  select : List (S × X) → Fin I

def TestingAdmissible {S : Type v} {X : Type w} {I : ℕ}
    (π : TestingPolicy S X I) : Prop := ∀ h, ∑' s, π.disp h s = 1

/-- Finite-dimensional history law, the product of adaptive experiment masses
and conditionally independent outcome masses. -/
noncomputable def testingPathProb {Θ : Type u} {S : Type v} {X : Type w} {I : ℕ}
    (M : TestingModel Θ S X I) (π : TestingPolicy S X I) (θ : Θ) :
    List (S × X) → ℝ≥0∞
  | [] => 1
  | (s, x) :: h => testingPathProb M π θ h * π.disp h s * ENNReal.ofReal (M.mass θ s x)

def testingHist {S : Type v} {X : Type w} {t : ℕ}
    (v : Fin t → S × X) : List (S × X) := (List.ofFn v).reverse

def TestingSurvives {S : Type v} {X : Type w} {I : ℕ}
    (π : TestingPolicy S X I) (h : List (S × X)) : Prop :=
  ∀ j ≤ h.length, ¬ π.stop (h.drop j)

def TestingStopsAt {S : Type v} {X : Type w} {I : ℕ}
    (π : TestingPolicy S X I) (h : List (S × X)) : Prop :=
  π.stop h ∧ ∀ j, 1 ≤ j → j ≤ h.length → ¬ π.stop (h.drop j)

open Classical in
noncomputable def testingProbGT {Θ : Type u} {S : Type v} {X : Type w} {I : ℕ}
    (M : TestingModel Θ S X I) (π : TestingPolicy S X I) (θ : Θ) (t : ℕ) : ℝ≥0∞ :=
  ∑' v : Fin t → S × X,
    if TestingSurvives π (testingHist v) then testingPathProb M π θ (testingHist v) else 0

/-- The tail-sum expectation in `[0,∞]`. -/
noncomputable def testingExpTau {Θ : Type u} {S : Type v} {X : Type w} {I : ℕ}
    (M : TestingModel Θ S X I) (π : TestingPolicy S X I) (θ : Θ) : ℝ≥0∞ :=
  ∑' t : ℕ, testingProbGT M π θ t

open Classical in
noncomputable def testingProbStop {Θ : Type u} {S : Type v} {X : Type w} {I : ℕ}
    (M : TestingModel Θ S X I) (π : TestingPolicy S X I) (θ : Θ) : ℝ≥0∞ :=
  ∑' t : ℕ, ∑' v : Fin t → S × X,
    if TestingStopsAt π (testingHist v) then testingPathProb M π θ (testingHist v) else 0

open Classical in
noncomputable def testingProbWrong {Θ : Type u} {S : Type v} {X : Type w} {I : ℕ}
    (M : TestingModel Θ S X I) (π : TestingPolicy S X I) (θ : Θ) : ℝ≥0∞ :=
  ∑' t : ℕ, ∑' v : Fin t → S × X,
    if TestingStopsAt π (testingHist v) ∧ θ ∉ M.H (π.select (testingHist v))
    then testingPathProb M π θ (testingHist v) else 0

/-- Appendix B.1, p.45: a.s. termination and error at most δ at every parameter. -/
def TestingDeltaAccurate {Θ : Type u} {S : Type v} {X : Type w} {I : ℕ}
    (M : TestingModel Θ S X I) (δ : ℝ) (π : TestingPolicy S X I) : Prop :=
  TestingAdmissible π ∧ ∀ θ, testingProbStop M π θ = 1 ∧
    testingProbWrong M π θ ≤ ENNReal.ofReal δ

def TestingAccurate {Θ : Type u} {S : Type v} {X : Type w} {I : ℕ}
    (M : TestingModel Θ S X I) (fam : ℝ → TestingPolicy S X I) : Prop :=
  ∀ δ ∈ Set.Ioo (0 : ℝ) 1, TestingDeltaAccurate M δ (fam δ)

noncomputable def testingLowerRate {Θ : Type u} {S : Type v} {X : Type w} {I : ℕ}
    (M : TestingModel Θ S X I) (fam : ℝ → TestingPolicy S X I) (θ : Θ) : ℝ≥0∞ :=
  Filter.liminf (fun δ : ℝ => testingExpTau M (fam δ) θ /
    ENNReal.ofReal (Real.log (1 / δ))) (𝓝[>] 0)

end RobustPrefLearn.MTP.Supplement


