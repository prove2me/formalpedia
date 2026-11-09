-- Prove2me | Definitions.Def_IdentityTesting39_ExactRadius_StatisticalModel
-- name    : IdentityTesting39_ExactRadius_StatisticalModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:52:17.827769+00:00
-- url     : https://prove2.me/theorems/e4fad634-b445-48d4-a9f0-48a80353e588
-- title:
--   Finite identity tests and fixed-sample complexity
-- statement:
--   Let $\iota$ be a finite label set and let $p,q$ be probability vectors: nonnegative real coordinates summing to one. This uses Mathlib's probability simplex. Total variation is the published finite-vector distance $\operatorname{TV}(p,q)=\frac12\sum_i|p_i-q_i|$.
--
--   A radius is nonempty and strict when $\varepsilon>0$ and some probability vector satisfies $\operatorname{TV}(p,q)>\varepsilon$. For $m$ independent observations, a randomized test is a rejection-probability function $f:\iota^m\to[0,1]$. Its expectation is the finite sum weighted by $\prod_{j=1}^m p_{x_j}$. It is admissible when
--
--   $$\mathbb E_{q^m}f\le\tfrac13,\qquad \mathbb E_{p^m}(1-f)\le\tfrac13\quad\text{for every }\operatorname{TV}(p,q)>\varepsilon.$$
--
--   The set of admissible sample counts and its natural-number infimum define $N^*(q,\varepsilon)$. A largest label has reference mass at least that of every other label. Randomization follows the explicit usage in Appendix A. The empty infimum is zero; the goal separately asserts nonemptiness at every nonempty strict radius. This interface keeps the statistical quantity independent of the convex programs.
-- source:
--   Zhijie Zheng, An Exact-Radius Convex Characterization of Discrete Identity Testing, STOC 2027 submission #39 (October 2026), p.2, §2, statistical conventions (randomization: Appendix A, p.15); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/39.pdf

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Divergences

open scoped BigOperators

noncomputable section

namespace IdentityTesting39.ExactRadius

/-- The probability simplex is Mathlib's general finite probability-vector object. -/
abbrev ProbabilityVector {ι : Type} [Fintype ι] (p : ι → ℝ) : Prop :=
  p ∈ stdSimplex ℝ ι

/-- A strict radius is nonempty precisely when an alternative exists. -/
def StrictRadius {ι : Type} [Fintype ι] (q : ι → ℝ) (ε : ℝ) : Prop :=
  0 < ε ∧ ∃ p : ι → ℝ, ProbabilityVector p ∧ ε < FoundationsRL.GeneralDM.totalVariationDiscrete p q

/-- Expectation under the m-fold iid law, expressed as a finite sum. -/
noncomputable def sampleExpectation {ι : Type} [Fintype ι] (p : ι → ℝ)
    (m : ℕ) (f : (Fin m → ι) → ℝ) : ℝ :=
  ∑ x : Fin m → ι, (∏ j, p (x j)) * f x

/-- Randomized rejection-probability functions; both errors are at most 1/3. -/
def AdmissibleTest {ι : Type} [Fintype ι] (q : ι → ℝ) (ε : ℝ)
    (m : ℕ) (f : (Fin m → ι) → ℝ) : Prop :=
  (∀ x, f x ∈ Set.Icc 0 1) ∧ sampleExpectation q m f ≤ 1 / 3 ∧
    ∀ p, ProbabilityVector p → ε < FoundationsRL.GeneralDM.totalVariationDiscrete p q →
      sampleExpectation p m (fun x => 1 - f x) ≤ 1 / 3

def admissibleSizes {ι : Type} [Fintype ι] (q : ι → ℝ) (ε : ℝ) : Set ℕ :=
  {m | ∃ f, AdmissibleTest q ε m f}

/-- §2: the least admissible fixed sample count; zero on the empty set. -/
noncomputable def sampleComplexity {ι : Type} [Fintype ι] (q : ι → ℝ) (ε : ℝ) : ℕ :=
  sInf (admissibleSizes q ε)

def Largest {ι : Type} (q : ι → ℝ) (i₀ : ι) : Prop := ∀ i, q i ≤ q i₀

end IdentityTesting39.ExactRadius


