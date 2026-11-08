-- Prove2me | Definitions.Def_SpencerEight_PeakedDensityComparison
-- name    : SpencerEight_PeakedDensityComparison
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:12:37.400937+00:00
-- url     : https://prove2.me/theorems/248bb7bc-f04f-45a7-b424-742fd3c81052
-- title:
--   Conclusions of Lemma 8.2 at $(s,a)$
-- statement:
--   For the law $P$ of $Z+s\sigma$ with density parameters $(s,a)$, this is the conjunction of:
--
--   1. $P$ has an even density nonincreasing on $[0,\infty)$;
--   2. $P([-x,x])\ge\gamma_1([-x,x])$ for every $x\ge0$;
--   3. $P^{\otimes m}(K)\ge\gamma_m(K)$ for every $m$ and every symmetric convex Borel set $K\subseteq\mathbb R^m$.
--
--   It is one predicate because Lemma 8.42 asserts the same conclusions at the refined parameters.
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Lemma 8.2, p.69 (PDF p.69); Lemma 8.42, p.104 (PDF p.104)

import Mathlib
import Definitions.Def_SpencerEight_gammaM
import Definitions.Def_SpencerEight_translatedLaw
open MeasureTheory ProbabilityTheory

namespace SpencerEight

/-- The three conclusions of Lemma 8.2 (Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), p.69 (PDF p.69)), for the law `P` of `Z + sσ` with density parameters `(s, a)`: `P` has an even density nonincreasing on `[0, ∞)`; `P([−x, x]) ≥ γ₁([−x, x])` for `x ≥ 0`; and `P^{⊗m}(K) ≥ γ_m(K)` for every symmetric convex Borel `K ⊆ ℝ^m`. Stated as one predicate because Lemma 8.42 asserts the same conclusions at other parameters.

**Formalization Note** `m = 0` is allowed. Symmetric means `K = −K`, written as `x ∈ K → −x ∈ K`, which is equivalent. -/
def PeakedDensityComparison (s a : ℝ) : Prop :=
  (∃ f : ℝ → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧
      translatedLaw s a = volume.withDensity (fun x => ENNReal.ofReal (f x)) ∧
      (∀ x, f (-x) = f x) ∧ AntitoneOn f (Set.Ici 0)) ∧
  (∀ x : ℝ, 0 ≤ x →
      gaussianReal 0 1 (Set.Icc (-x) x) ≤ translatedLaw s a (Set.Icc (-x) x)) ∧
  (∀ (m : ℕ) (K : Set (Fin m → ℝ)), MeasurableSet K → Convex ℝ K → (∀ x ∈ K, -x ∈ K) →
      gammaM (Fin m) K ≤ Measure.pi (fun _ : Fin m => translatedLaw s a) K)

end SpencerEight


