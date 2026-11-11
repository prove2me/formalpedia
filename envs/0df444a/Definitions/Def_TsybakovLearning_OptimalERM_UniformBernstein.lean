-- Prove2me | Definitions.Def_TsybakovLearning_OptimalERM_UniformBernstein
-- name    : TsybakovLearning_OptimalERM_UniformBernstein
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:53:26.824814+00:00
-- url     : https://prove2.me/theorems/995ba5bc-ac2c-4e0e-a04a-a03dd76f1e25
-- title:
--   Universal region-sensitive Bernstein property of a numerical constant
-- statement:
--   For a real number $c$, the universal Bernstein property says that, for every measurable instance space $X$, class $H$ under the stated empirical-process measurability convention, probability law $D$, finite VC dimension $d$, measurable region $\Delta$, positive sample size $m$, and confidence $0<\delta<1$, the failure event defined by the exact Lemma 2 inequality satisfies
--
--   $$D^m\{S:\exists f,g\in H,\ |(\mathrm{er}_{D,\Delta}(f)-\mathrm{er}_{D,\Delta}(g))-(\widehat{\mathrm{er}}_{S,\Delta}(f)-\widehat{\mathrm{er}}_{S,\Delta}(g))|>B_2\}\le\delta.$$
--
--   All these failure sets are stipulated measurable for every numerical coefficient, independently of c. Lemma 2 asserts that some positive numerical c has this property. Lemma 3 keeps this very same property attached to its existential numerical witness, so its coefficient cannot vary between instances.
--
--   **Formalization Note** This is a definition of a proposition, with its full inequality in the body. It is not a model hypothesis, an axiom, or an asserted theorem; its existence is the separate Lemma 2 obligation. The goal assumes no concentration property. The fixed Lean universe is the only parameter outside the universal numerical witness.
-- source:
--   Steve Hanneke, Hongao Wang, Mingyue Xu, STOC 2027 submission #1413 (October 2026), Lemma 2, pp. 5–6 (PDF pp. 5–6); shared constant in Lemma 3, p. 6 (PDF p. 6)

import Definitions.Def_TsybakovLearning_OptimalERM_ProbabilityConvention

open MeasureTheory
universe uBernstein

namespace TsybakovLearning.OptimalERM

/-- The full universal property asserted by Lemma 2, named so Lemma 3 can use the SAME c.
It is a predicate to be proved, not a field of the statistical model or an assumed axiom. -/
def UniformBernstein (c : ℝ) : Prop :=
  ∀ (X : Type uBernstein) [MeasurableSpace X] (H : Set (X → Bool))
    (D : Measure (X × Bool)) [IsProbabilityMeasure D],
    MeasurableClass H D → ∀ d : ℕ, UnderstandingML.vcDim H = (d : ℕ∞) →
    ∀ Δ : Set X, MeasurableSet Δ → ∀ m : ℕ, 0 < m →
    ∀ δ : ℝ, 0 < δ → δ < 1 →
    (∀ b : ℝ, MeasurableSet (bernsteinFailure b H D Δ d m δ)) →
      UnderstandingML.iidLaw D m (bernsteinFailure c H D Δ d m δ) ≤ ENNReal.ofReal δ

end TsybakovLearning.OptimalERM


