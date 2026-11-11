-- Prove2me | Definitions.Def_TsybakovLearning_OptimalERM_ProbabilityConvention
-- name    : TsybakovLearning_OptimalERM_ProbabilityConvention
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:52:34.334213+00:00
-- url     : https://prove2.me/theorems/1cc47653-fad0-471b-b65d-cd181994d092
-- title:
--   Measurable empirical processes and localized loss differences
-- statement:
--   For a class $\mathcal F$ of real functions on a measurable space $Z$, empirical-process measurability means that, for every finite number $k$ of observations, every real vector $(w_i)_{i=1}^k$, and every threshold $t$, the supremum threshold event
--
--   $$\left\{(z_i)_{i=1}^k:\exists f\in\mathcal F,\ t<\sum_{i=1}^k w_if(z_i)\right\}$$
--
--   is measurable in the product sigma algebra. This includes signed differences formed with independent ghost observations, rather than only one-observation loss measurability.
--
--   Here the measurable-class convention requires every $h\in H$ to be measurable and requires that property for the restricted loss-difference classes below. Put $\ell_{h,\Delta}(x,y)=\mathbf1\{x\in\Delta,h(x)\ne y\}$. For each measurable $\Delta$, comparator class $G=H$ or $G=\{g_0\}$ with $g_0\in H$, and real $r,b$ and $\kappa\in\{0,1\}$, the functions are
--
--   $$z\longmapsto \ell_{f,\Delta}(z)-\ell_{g,\Delta}(z)-\kappa\bigl(\mathrm{er}_{D,\Delta}(f)-\mathrm{er}_{D,\Delta}(g)\bigr),$$
--
--   where $f\in H$, $g\in G$, disagreement on $\Delta$ is at most $r$, and restricted signed excess is at most $b$. Thus $\kappa=0$ gives uncentered functions and $\kappa=1$ gives centered functions.
--
--   This explicitly reads the paper's measurable class and Appendix A's measurable localized classes in the ordinary empirical-process sense. It imposes neither countability nor pointwise separability, no topology on X, and no concentration bound. The theorems additionally state measurability of the exact probability events, for all thresholds independently of the chosen constants. The centered functions are not asserted to vanish outside $\Delta$.
-- source:
--   Steve Hanneke, Hongao Wang, Mingyue Xu, STOC 2027 submission #1413 (October 2026), Lemma 2, pp. 5–6 (PDF pp. 5–6); Appendix A, pp. 14–15 (PDF pp. 14–15)

import Definitions.Def_TsybakovLearning_OptimalERM_Bounds

open MeasureTheory

namespace TsybakovLearning.OptimalERM

variable {Z : Type*} [MeasurableSpace Z]

/-- Ordinary empirical-process measurability: finite signed sums have measurable supremum
threshold events, including on samples containing independent ghost observations. No bound
on these events' probabilities is part of this predicate. -/
def EmpiricalMeasurable (F : Set (Z → ℝ)) : Prop :=
  ∀ (k : ℕ) (w : Fin k → ℝ) (t : ℝ),
    MeasurableSet {S : Fin k → Z | ∃ f ∈ F, t < ∑ i, w i * f (S i)}

variable {X : Type*} [MeasurableSpace X]

/-- Restricted loss differences, localized by population disagreement and signed mean.
κ=0 gives the original functions; κ=1 gives their centered versions. -/
def localizedDifferences (H G : Set (X → Bool)) (D : Measure (X × Bool))
    (Δ : Set X) (r b κ : ℝ) : Set ((X × Bool) → ℝ) :=
  {v | ∃ f ∈ H, ∃ g ∈ G, disagreement D Δ f g ≤ r ∧
    restrictedRisk D Δ f - restrictedRisk D Δ g ≤ b ∧
    v = fun z => restrictedLoss Δ f z - restrictedLoss Δ g z -
      κ * (restrictedRisk D Δ f - restrictedRisk D Δ g)}

/-- The ordinary measurable-class reading of Lemma 2 and Appendix A, pp. 14–15:
measurable hypotheses and empirical suprema of the restricted, localized difference classes
and their centered versions. Comparators range over H or one fixed member of H.
This is a measurability convention, not countability, separability, or a concentration claim. -/
def MeasurableClass (H : Set (X → Bool)) (D : Measure (X × Bool)) : Prop :=
  (∀ h ∈ H, Measurable h) ∧
  ∀ (Δ : Set X), MeasurableSet Δ → ∀ G : Set (X → Bool),
    (G = H ∨ ∃ g ∈ H, G = {g}) → ∀ r b : ℝ,
      EmpiricalMeasurable (localizedDifferences H G D Δ r b 0) ∧
      EmpiricalMeasurable (localizedDifferences H G D Δ r b 1)

end TsybakovLearning.OptimalERM


